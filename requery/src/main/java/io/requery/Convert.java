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

package io.requery;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

/**
 * Used to specify a {@link Converter} for a field or method that is mapped to an {@link Entity}
 * attribute. The converter will be created per field and implementations much have a zero-arg
 * constructor.
 *
 * @see Converter
 */
@Documented
@Target({FIELD, METHOD})
@Retention(RUNTIME)
public @interface Convert {

    /**
     * @return The class implementing the {@link Converter} interface.
     */
    Class<? extends Converter> value();
}
