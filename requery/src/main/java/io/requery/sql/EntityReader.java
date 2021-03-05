/*
 * Copyright 2016 requery.io
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package io.requery.sql;

import io.requery.CascadeAction;
import io.requery.EntityCache;
import io.requery.PersistenceException;
import io.requery.Queryable;
import io.requery.meta.Attribute;
import io.requery.meta.Cardinality;
import io.requery.meta.QueryAttribute;
import io.requery.meta.Type;
import io.requery.proxy.CollectionChanges;
import io.requery.proxy.CompositeKey;
import io.requery.proxy.EntityBuilderProxy;
import io.requery.proxy.EntityProxy;
import io.requery.proxy.Initializer;
import io.requery.proxy.Property;
import io.requery.proxy.PropertyLoader;
import io.requery.proxy.PropertyState;
import io.requery.proxy.QueryInitializer;
import io.requery.proxy.Settable;
import io.requery.query.AliasedExpression;
import io.requery.query.Condition;
import io.requery.query.Expression;
import io.requery.query.Functional;
import io.requery.query.Result;
import io.requery.query.Tuple;
import io.requery.query.WhereAndOr;
import io.requery.query.element.QueryElement;
import io.requery.query.element.QueryType;
import io.requery.util.FilteringIterator;
import io.requery.util.Objects;
import io.requery.util.ObservableCollection;
import io.requery.util.function.Consumer;
import io.requery.util.function.Predicate;
import io.requery.util.function.Supplier;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static io.requery.sql.Keyword.AS;
import static io.requery.sql.Keyword.FROM;
import static io.requery.sql.Keyword.SELECT;
import static io.requery.sql.Keyword.WHERE;

/**
 * Handles refreshing and loading attributes for {@link io.requery.Entity} instances.
 *
 * @param <E> the entity type
 * @param <S> generic type from which all entities extend
 * @author Nikhil Purushe
 */
class EntityReader<E extends S, S> implements PropertyLoader<E> {

    private final EntityCache cache;
    private final Type<E> type;
    private final Mapping mapping;
    private final EntityContext<S> context;
    private final Queryable<S> queryable;
    private final QueryAttribute<E, ?> keyAttribute;
    private final boolean stateless;
    private final boolean cacheable;
    private final Set<Expression<?>> defaultSelection;
    private final Attribute<E, ?>[] defaultSelectionAttributes;

    EntityReader(Type<E> type, EntityContext<S> context, Queryable<S> queryable) {
        this.type = Objects.requireNotNull(type);
        this.context = Objects.requireNotNull(context);
        this.queryable = Objects.requireNotNull(queryable);
        this.cache = this.context.getCache();
        this.mapping = this.context.getMapping();
        this.stateless = type.isStateless();
        this.cacheable = type.isCacheable();
        // compute default/minimum selections for the type
        LinkedHashSet<Expression<?>> selection = new LinkedHashSet<>();
        LinkedHashSet<Attribute<E, ?>> selectAttributes = new LinkedHashSet<>();
        for (Attribute<E, ?> attribute : type.getAttributes()) {
            // include foreign or primary key
            boolean isKey = (attribute.isForeignKey() || attribute.isKey());
            if (!attribute.isLazy() && (isKey || !attribute.isAssociation())) {
                if (attribute.isVersion()) {
                    Expression<?> expression = aliasVersion(attribute);
                    selection.add(expression);
                } else {
                    selection.add((Expression) attribute);
                }
                selectAttributes.add(attribute);
            }
        }
        defaultSelection = Collections.unmodifiableSet(selection);
        // optimization for single key attribute
        keyAttribute = Attributes.query(type.getSingleKeyAttribute());
        // attributes converted to array for performance
        defaultSelectionAttributes = Attributes.toArray(selectAttributes,
                new Predicate<Attribute<E, ?>>() {
                    @Override
                    public boolean test(Attribute<E, ?> value) {
                        return true;
                    }
                });
    }

    Set<Expression<?>> defaultSelection() {
        return defaultSelection;
    }

    Attribute<E, ?>[] defaultSelectionAttributes() {
        return defaultSelectionAttributes;
    }

    ResultReader<E> newResultReader(Attribute[] attributes) {
        if (type.isBuildable()) {
            return new BuildableEntityResultReader<>(this, attributes);
        } else {
            return new EntityResultReader<>(this, attributes);
        }
    }

    private Expression aliasVersion(Attribute attribute) {
        // special handling for system version column
        String columnName = context.getPlatform().versionColumnDefinition().columnName();
        if (attribute.isVersion() && columnName != null) {
            Expression<?> expression = (Expression<?>) attribute;
            return new AliasedExpression<>(expression, columnName, expression.getName());
        }
        return (Expression) attribute;
    }

    @Override
    public <V> void load(E entity, EntityProxy<E> proxy, Attribute<E, V> attribute) {
        refresh(entity, proxy, attribute);
    }

    public E refresh(E entity, EntityProxy<E> proxy) {
        // refresh only the attributes that were loaded...
        final Set<Attribute<E, ?>> refreshAttributes = new LinkedHashSet<>();
        for (Attribute<E, ?> attribute : type.getAttributes()) {
            if (stateless || proxy.getState(attribute) == PropertyState.LOADED) {
                refreshAttributes.add(attribute);
            }
        }
        return refresh(entity, proxy, refreshAttributes);
    }

    public E refreshAll(E entity, EntityProxy<E> proxy) {
        return refresh(entity, proxy, type.getAttributes());
    }

    @SafeVarargs
    public final E refresh(E entity, EntityProxy<E> proxy, Attribute<E, ?>... attributes) {
        if (attributes == null || attributes.length == 0) {
            return entity;
        }
        Set<Attribute<E, ?>> elements;
        if (attributes.length == 1) {
            elements = Collections.<Attribute<E, ?>>singleton(attributes[0]);
        } else {
            elements = new LinkedHashSet<>(attributes.length);
            Collections.addAll(elements, attributes);
        }
        return refresh(entity, proxy, elements);
    }

    private E refresh(E entity, EntityProxy<E> proxy, final Set<Attribute<E, ?>> attributes) {

        Predicate<Attribute<E, ?>> basicFilter = new Predicate<Attribute<E, ?>>() {
            @Override
            public boolean test(Attribute<E, ?> value) {
                return attributes.contains(value) &&
                        (!value.isAssociation() || value.isForeignKey());
            }
        };
        FilteringIterator<Attribute<E, ?>> filterator =
                new FilteringIterator<>(attributes.iterator(), basicFilter);
        if (filterator.hasNext()) {
            QueryBuilder qb = new QueryBuilder(context.getQueryBuilderOptions())
                    .keyword(SELECT)
                    .commaSeparated(filterator, new QueryBuilder.Appender<Attribute<E, ?>>() {
                        @Override
                        public void append(QueryBuilder qb, Attribute<E, ?> value) {
                            String versionColumn = context.getPlatform()
                                    .versionColumnDefinition().columnName();
                            if (value.isVersion() && versionColumn != null) {
                                qb.append(versionColumn).space()
                                        .append(AS).space()
                                        .append(value.getName()).space();
                            } else {
                                qb.attribute(value);
                            }
                        }
                    })
                    .keyword(FROM)
                    .tableName(type.getName())
                    .keyword(WHERE)
                    .appendWhereConditions(type.getKeyAttributes());

            String sql = qb.toString();
            try (Connection connection = context.getConnection();
                 PreparedStatement statement = connection.prepareStatement(sql)) {
                int index = 1;
                for (Attribute<E, ?> attribute : type.getKeyAttributes()) {
                    Object value = proxy.getKey(attribute);
                    if (value == null) {
                        throw new MissingKeyException(proxy);
                    }
                    mapping.write((Expression) attribute, statement, index++, value);
                }
                context.getStatementListener().beforeExecuteQuery(statement, sql, null);
                ResultSet results = statement.executeQuery();
                context.getStatementListener().afterExecuteQuery(statement);
                if (results.next()) {
                    Attribute[] selection = new Attribute[attributes.size()];
                    attributes.toArray(selection);
                    // if the type is immutable create a new entity and return it, otherwise
                    // modify the given entity
                    if (type.isImmutable()) {
                        entity = fromBuilder(results, selection);
                    } else {
                        entity = fromResult(entity, results, selection);
                    }
                }
            } catch (SQLException e) {
                throw new PersistenceException(e);
            }
        }
        // refresh associations
        for (Attribute<E, ?> attribute : attributes) {
            // if it's a foreign key its resolved as part of the basic properties
            if (attribute.isAssociation()) {
                refreshAssociation(entity, proxy, attribute);
            }
        }
        return entity;
    }

    private void refreshAssociation(E entity, EntityProxy<E> proxy, Attribute<E, ?> attribute) {
        Supplier<? extends Result<S>> query = associativeQuery(proxy, attribute);
        switch (attribute.getCardinality()) {
            case ONE_TO_ONE:
            case MANY_TO_ONE:
                refreshAssociationToOne(entity, proxy, (Attribute<E, S>) attribute);
            break;
            case ONE_TO_MANY:
            case MANY_TO_MANY:
                refreshAssociationToMany(entity,proxy,(Attribute<E,Collection<S>>) attribute);
            break;
            default:
                throw new IllegalStateException();
        }
    }
    private <V extends S> void refreshAssociationToOne(E entity, EntityProxy<E> proxy, Attribute<E, V> attribute) {
        Supplier<? extends Result<V>> query = associativeQuery(proxy, attribute);
        V mappedEntity = query == null ? null : query.get().firstOrNull();
        proxy.set(attribute, mappedEntity, PropertyState.LOADED);
        addCascadeListenerToOne(entity, proxy, attribute, mappedEntity);
    }
    private <V extends S , COL extends Collection<V>> void refreshAssociationToMany(E entity, EntityProxy<E> proxy, Attribute<E, COL> attribute) {
        Supplier<? extends Result<V>> query = associativeQuery(proxy, attribute);
        Initializer<E, COL> initializer = attribute.getInitializer();
        if (initializer instanceof QueryInitializer) {
            QueryInitializer<E, COL> queryInitializer = (QueryInitializer<E,COL>) initializer;
            COL result = queryInitializer.initialize(proxy, attribute, query);
            proxy.set(attribute, result, PropertyState.LOADED);
            for (V mappedEntity : result) {
                addCascadeListenerToMany(entity,proxy,attribute, mappedEntity);
            }
        }
    }



        private <Q extends S> Supplier<? extends Result<Q>>
    associativeQuery(EntityProxy<E> proxy, Attribute<E, ?> attribute) {
        switch (attribute.getCardinality()) {
            case ONE_TO_ONE:
            case ONE_TO_MANY:
            case MANY_TO_ONE: {
                Object key;
                QueryAttribute<Q, Object> keyAttribute;
                Class<Q> uType;
                if (attribute.isForeignKey()) {
                    keyAttribute = Attributes.get(attribute.getReferencedAttribute());
                    uType = keyAttribute.getDeclaringType().getClassType();
                    Q entity = uType.cast(proxy.get(attribute, false));
                    if (entity == null) {
                        return null;
                    }
                    EntityProxy<Q> referredProxy = context.getModel()
                            .typeOf(uType).getProxyProvider().apply(entity);

                    key = referredProxy.get(keyAttribute);
                } else {
                    keyAttribute = Attributes.get(attribute.getMappedAttribute());
                    uType = keyAttribute.getDeclaringType().getClassType();
                    Attribute<E, ?> referenced = Attributes.get(
                            keyAttribute.getReferencedAttribute());
                    key = proxy.get(referenced);
                }
                return order(queryable.select(uType).where(keyAttribute.equal(key)),
                        attribute.getOrderByAttribute());
            }
            case MANY_TO_MANY: {
                @SuppressWarnings("unchecked")
                Class<Q> uType = (Class<Q>) attribute.getElementClass();
                QueryAttribute<E, Object> tKey = null;
                QueryAttribute<Q, Object> uKey = null;
                Type<?> junctionType = context.getModel().typeOf(attribute.getReferencedClass());
                for (Attribute a : junctionType.getAttributes()) {
                    Class referenceType = a.getReferencedClass();
                    if (referenceType != null) {
                        if (tKey == null && type.getClassType().isAssignableFrom(referenceType)) {
                            tKey = Attributes.query(a);
                        } else if (uType.isAssignableFrom(referenceType)) {
                            uKey = Attributes.query(a);
                        }
                    }
                }
                Objects.requireNotNull(tKey);
                Objects.requireNotNull(uKey);
                QueryAttribute<E, Object> tId = Attributes.get(tKey.getReferencedAttribute());
                QueryAttribute<Q, Object> uId = Attributes.get(uKey.getReferencedAttribute());
                Object id = proxy.get(tId);
                if (id == null) {
                    throw new IllegalStateException();
                }
                // create the many to many join query
                return order(queryable.select(uType)
                        .join(junctionType.getClassType()).on(uId.equal(uKey))
                        .join(type.getClassType()).on(tKey.equal(tId))
                        .where(tId.equal(id)), attribute.getOrderByAttribute());
            }
            default:
                throw new IllegalStateException();
        }
    }

    private <Q extends S> Supplier<? extends Result<Q>>
    order(WhereAndOr<? extends Result<Q>> query, Supplier<Attribute> supplier) {
        if (supplier != null) {
            Attribute attribute = supplier.get();
            if (attribute.getOrderByDirection() != null && attribute instanceof Functional) {
                switch (attribute.getOrderByDirection()) {
                    case ASC:
                        query.orderBy(((Functional) attribute).asc());
                        break;
                    case DESC:
                        query.orderBy(((Functional) attribute).desc());
                        break;
                }
            } else {
                query.orderBy((Expression) attribute);
            }
        }
        return query;
    }

    @SafeVarargs
    final Iterable<E> batchRefresh(Iterable<E> entities, Attribute<E, ?>... attributes) {
        // if the type is immutable return a new collection with the rebuilt objects
        final Collection<E> collection = type.isImmutable() ? new ArrayList<E>() : null;

        if (keyAttribute == null) {
            // non optimal case objects with multiple keys or no keys
            for (E entity : entities) {
                entity = refresh(entity, type.getProxyProvider().apply(entity), attributes);
                if (collection != null) {
                    collection.add(entity);
                }
            }
        } else {
            Set<Expression<?>> selection = new LinkedHashSet<>();
            Attribute[] selectAttributes;
            if (attributes == null || attributes.length == 0) {
                selection = defaultSelection;
                selectAttributes = defaultSelectionAttributes;
            } else {
                LinkedHashSet<Attribute> selectedAttributes = new LinkedHashSet<>();
                selection.add(keyAttribute);
                selectedAttributes.add(keyAttribute);
                for (Attribute<E, ?> attribute : attributes) {
                    if (attribute.isVersion()) {
                        selection.add(aliasVersion(attribute));
                    } else if (!attribute.isAssociation()) {
                        QueryAttribute<E, ?> queryAttribute = Attributes.query(attribute);
                        selection.add(queryAttribute);
                    }
                    selectedAttributes.add(attribute);
                }
                selectAttributes = selectedAttributes.toArray(new Attribute[selection.size()]);
            }
            Map<Object, EntityProxy<E>> map = new HashMap<>();
            Map<Object, E> entitiesMap = new HashMap<>();
            for (E entity : entities) {
                EntityProxy<E> proxy = type.getProxyProvider().apply(entity);
                Object key = proxy.key();
                if (key == null) {
                    throw new MissingKeyException();
                }
                map.put(key, proxy);
                entitiesMap.put(key, entity);
            }
            Condition<?, ?> condition = Attributes.query(keyAttribute).in(map.keySet());
            if (type.isCacheable()) {
                final Consumer<E> collector = new Consumer<E>() {
                    @Override
                    public void accept(E e) {
                        if (collection != null) {
                            collection.add(e);
                        }
                    }
                };
                // readResult will merge the results into the target object in cache mode
                ResultReader<E> resultReader = newResultReader(selectAttributes);

                SelectOperation<E> select = new SelectOperation<>(context, resultReader);
                QueryElement<? extends Result<E>> query =
                        new QueryElement<>(QueryType.SELECT, context.getModel(), select);

                try (Result<E> result = query.select(selection).where(condition).get()) {
                    result.each(collector);
                }
            } else {
                try (Result<Tuple> result = queryable.select(selection).where(condition).get()) {
                    for (Tuple tuple : result) {
                        Object key = tuple.get((Expression) keyAttribute);
                        EntityProxy<E> proxy = map.get(key);
                        synchronized (proxy.syncObject()) {
                            for (Expression expression : selection) {
                                Object value = tuple.get(expression);
                                if (expression instanceof AliasedExpression) {
                                    AliasedExpression aliased = (AliasedExpression) expression;
                                    expression = aliased.getInnerExpression();
                                }
                                Attribute<E, Object> attribute =
                                        Attributes.query((Attribute) expression);
                                proxy.set(attribute, value, PropertyState.LOADED);
                            }
                        }
                    }
                }
            }
            // associations TODO can be optimized
            if (attributes != null) {
                for (Attribute<E, ?> attribute : attributes) {
                    if (attribute.isAssociation()) {
                        for (Object key : map.keySet()) {
                            refreshAssociation(entitiesMap.get(key), map.get(key), attribute);
                        }
                    }
                }
            }
        }
        return collection == null ? entities : collection;
    }

    private E createEntity() {
        E entity = type.getFactory().get();
        EntityProxy<E> proxy = type.getProxyProvider().apply(entity);
        proxy.link(this);
        return entity;
    }

    private Object readCacheKey(ResultSet results) throws SQLException {
        Object key = null;
        if (keyAttribute != null) { // common case 1 primary key
            key = readKey(keyAttribute, results, results.findColumn(keyAttribute.getName()));
        } else {
            int count = type.getKeyAttributes().size();
            if (count > 1) {
                LinkedHashMap<Attribute<E, ?>, Object> keys = new LinkedHashMap<>(count);
                for (Attribute<E, ?> attribute : type.getKeyAttributes()) {
                    String name = attribute.getName();
                    Object value = readKey(attribute, results, results.findColumn(name));
                    keys.put(attribute, value);
                }
                key = new CompositeKey<>(keys);
            }
        }
        return key;
    }

    private Object readKey(Attribute<E, ?> attribute, ResultSet results, int index)
            throws SQLException {
        Attribute referenced = attribute;
        if (attribute.isAssociation()) {
            // in the case of a foreign key referenced read the type of the key in the other type
            referenced = Attributes.get(attribute.getReferencedAttribute());
        }
        return mapping.read((Expression) referenced, results, index);
    }

    final E fromResult(E entity, ResultSet results, Attribute[] selection) throws SQLException {
        // if refreshing (entity not null) overwrite the properties
        boolean overwrite = entity != null || stateless;

        if (entity == null) {
            // get or create the entity object
            if (cacheable) {
                synchronized (type) {
                    // try lookup cached object
                    final Object key = readCacheKey(results);
                    if (key != null) {
                        entity = cache.get(type.getClassType(), key);
                    }
                    // not cached create a new one
                    if (entity == null) {
                        entity = createEntity();
                        if (key != null) {
                            cache.put(type.getClassType(), key, entity);
                        }
                    }
                }
            } else {
                entity = createEntity();
            }
        }

        // set the properties
        EntityProxy<E> proxy = type.getProxyProvider().apply(entity);
        synchronized (proxy.syncObject()) {
            proxy.link(this);
            int index = 1;
            for (Attribute expression : selection) {
                @SuppressWarnings("unchecked")
                Attribute<E, ?> attribute = (Attribute<E, ?>) expression;
                boolean isAssociation = attribute.isAssociation();

                if ((attribute.isForeignKey() || attribute.isKey()) && isAssociation) {
                    // handle loading the foreign key into referenced object
                    Attribute referenced = Attributes.get(attribute.getReferencedAttribute());

                    Object key = mapping.read((Expression) referenced, results, index);
                    if (key != null) {
                        Object value = proxy.get(attribute, false);
                        if (value == null) {
                            // create one...
                            Class classType = attribute.getClassType();
                            EntityReader reader = context.read(classType);
                            value = reader.createEntity();
                        }
                        EntityProxy<Object> mappedProxy = context.proxyOf(value, false);
                        mappedProxy.set(Attributes.get(attribute.getReferencedAttribute()), key,
                                PropertyState.LOADED);

                        // leave in fetch state if only key is loaded
                        PropertyState state = stateless ? PropertyState.LOADED : proxy.getState(attribute);
                        if (state != PropertyState.LOADED) {
                            state = PropertyState.FETCH;
                        }
                        proxy.setObject(attribute, value, state);
                    }
                } else if (isAssociation) {
                    continue;
                } else if (overwrite || proxy.getState(attribute) != PropertyState.MODIFIED) {
                    if (attribute.getPrimitiveKind() != null) {
                        readPrimitiveField(proxy, attribute, results, index);
                    } else {
                        Object value = mapping.read((Expression) attribute, results, index);
                        proxy.setObject(attribute, value, PropertyState.LOADED);
                    }
                }
                index++;
            }
        }
        context.getStateListener().postLoad(entity, proxy);
        return entity;
    }

    private <V extends S, COL extends  Collection<V>> void addCascadeListenerToMany(final E entity, final EntityProxy<E> proxy, final Attribute<E, COL> attribute, final V mappedEntity) {
        final EntityProxy<V> mappedProxy = context.proxyOf(mappedEntity, false);
        _addCascadeListenerToMany(mappedProxy,proxy,attribute,mappedEntity);
        _addCascadeListenerToMapped(entity,proxy,attribute,mappedProxy);

    }


        private <V extends S> void addCascadeListenerToOne(final E entity, final EntityProxy<E> proxy, final Attribute<E, V> attribute, final V mappedEntity) {
        if (mappedEntity != null) {
            final EntityProxy<V> mappedProxy = context.proxyOf(mappedEntity, false);
            _addCascadeListenerToOne(mappedProxy, proxy, attribute);
            _addCascadeListenerToMapped(entity,proxy,attribute,mappedProxy);
        }
    }

    private  <V extends S> void _addCascadeListenerToMapped(final E entity, final EntityProxy<E> proxy, final Attribute<E, ?> attribute, EntityProxy<V> mappedProxy) {
        if (attribute.getMappedAttribute() != null) {
            final Attribute<V, ?> mappedAttribute = Attributes.get(attribute.getMappedAttribute());
            if (mappedAttribute.getCardinality() == Cardinality.MANY_TO_ONE || mappedAttribute.getCardinality() == Cardinality.ONE_TO_ONE) {
                Attribute<V, E> mappedSimpleAttribute = (Attribute<V, E>) mappedAttribute;
                _addCascadeListenerToOne(proxy, mappedProxy, mappedSimpleAttribute);
            } else {
                Attribute<V, Collection<E>> mappedCollectionAttribute = (Attribute<V, Collection<E>>) mappedAttribute;
                _addCascadeListenerToMany(proxy, mappedProxy, mappedCollectionAttribute, entity);
            }
        }
    }



    /**
     * When proxy is notified of a change then corresponding element in the referencing collection is marked
     */
    private <V extends S, T extends S> void _addCascadeListenerToMany(final EntityProxy<T> proxy, final EntityProxy<V> oppositeProxy, final Attribute<V, ? extends Collection<T>> oppositeAttribute, final T entity) {
        if (oppositeAttribute.getCascadeActions().contains(CascadeAction.SAVE)) {
            //when proxy is m
            proxy.addCascadeModificationListener(oppositeProxy, new Runnable() {
                @Override
                public void run() {
                    if(oppositeProxy.getState(oppositeAttribute) != PropertyState.FETCH) {
                        ObservableCollection<T> collection = (ObservableCollection<T>) oppositeProxy.get(oppositeAttribute);  // Should distinct detached and unloaded (instead of fetch only)
                        if (collection instanceof ObservableCollection) {  //todo remove all cascade obsever when link are broken
                            collection.observer().elementModified(entity);
                        }
                    }
                }

                @Override
                public String toString() {
                    return oppositeAttribute.toString();
                }
            });
        }
    }

    /**
     * When proxy is modifier -> opposite property is marked
     */
    private <V extends  S, T extends S> void _addCascadeListenerToOne(final EntityProxy<T> proxy, final EntityProxy<V> oppositeProxy, final Attribute<V, T> oppositeAttribute) {
        if (oppositeAttribute.getCascadeActions().contains(CascadeAction.SAVE)) {
            proxy.addCascadeModificationListener(oppositeProxy, new Runnable() {
                @Override
                public void run() {
                    oppositeProxy.setState(oppositeAttribute, PropertyState.ASSOCIATED_IS_MODIFIED);
                }
                @Override
                public String toString() {
                    return oppositeAttribute.toString();
                }
            });
        }
    }



    final <B> E fromBuilder(ResultSet results, Attribute[] selection) throws SQLException {
        EntityBuilderProxy<B, E> proxy = new EntityBuilderProxy<>(type);
        int index = 1;
        for (Attribute expression : selection) {
            @SuppressWarnings("unchecked")
            Attribute<E, ?> attribute = (Attribute<E, ?>) expression;
            if (attribute.getPrimitiveKind() != null) {
                readPrimitiveField(proxy, attribute, results, index);
            } else {
                Object value = mapping.read((Expression) attribute, results, index);
                proxy.setObject(attribute, value, PropertyState.LOADED);
            }
            index++;
        }
        return proxy.build();
    }

    @SuppressWarnings("unchecked") // checked by primitiveKind
    private void readPrimitiveField(Settable<E> proxy,
                                    Attribute<E, ?> attribute,
                                    ResultSet results, int index) throws SQLException {
        switch (attribute.getPrimitiveKind()) {
            case INT:
                Attribute<E, Integer> intAttribute = (Attribute<E, Integer>) attribute;
                int intValue = mapping.readInt(results, index);
                proxy.setInt(intAttribute, intValue, PropertyState.LOADED);
                break;
            case LONG:
                Attribute<E, Long> longAttribute = (Attribute<E, Long>) attribute;
                long longValue = mapping.readLong(results, index);
                proxy.setLong(longAttribute, longValue, PropertyState.LOADED);
                break;
            case SHORT:
                Attribute<E, Short> shortAttribute = (Attribute<E, Short>) attribute;
                short shortValue = mapping.readShort(results, index);
                proxy.setShort(shortAttribute, shortValue, PropertyState.LOADED);
                break;
            case BYTE:
                Attribute<E, Byte> byteAttribute = (Attribute<E, Byte>) attribute;
                byte byteValue = mapping.readByte(results, index);
                proxy.setByte(byteAttribute, byteValue, PropertyState.LOADED);
                break;
            case BOOLEAN:
                Attribute<E, Boolean> booleanAttribute = (Attribute<E, Boolean>) attribute;
                boolean booleanValue = mapping.readBoolean(results, index);
                proxy.setBoolean(booleanAttribute, booleanValue, PropertyState.LOADED);
                break;
            case FLOAT:
                Attribute<E, Float> floatAttribute = (Attribute<E, Float>) attribute;
                float floatValue = mapping.readFloat(results, index);
                proxy.setFloat(floatAttribute, floatValue, PropertyState.LOADED);
                break;
            case DOUBLE:
                Attribute<E, Double> doubleAttribute = (Attribute<E, Double>) attribute;
                double doubleValue = mapping.readDouble(results, index);
                proxy.setDouble(doubleAttribute, doubleValue, PropertyState.LOADED);
                break;
        }
    }
}
