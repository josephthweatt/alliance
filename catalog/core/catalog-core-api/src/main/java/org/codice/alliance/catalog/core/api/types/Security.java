/**
 * Copyright (c) Codice Foundation
 *
 * <p>This is free software: you can redistribute it and/or modify it under the terms of the GNU
 * Lesser General Public License as published by the Free Software Foundation, either version 3 of
 * the License, or any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details. A copy of the GNU Lesser General Public
 * License is distributed along with this program and can be found at
 * <http://www.gnu.org/licenses/lgpl.html>.
 */
package org.codice.alliance.catalog.core.api.types;

/**
 * <b> This code is experimental. While this interface is functional and tested, it may change or be
 * removed in a future version of the library.</b>
 */
public abstract class Security {

  /** Attribute name for accessing the security classification for this Metacard. */
  public static final String CLASSIFICATION = "security.classification";

  /** Attribute name for accessing the security classification system for this Metacard. */
  public static final String CLASSIFICATION_SYSTEM = "security.classification-system";

  /** Attribute name for accessing the security code words for this Metacard. */
  public static final String CODEWORDS = "security.codewords";

  /** Attribute name for accessing the security dissemination controls for this Metacard. */
  public static final String DISSEMINATION_CONTROLS = "security.dissemination-controls";

  /** Attribute name for accessing other security dissemination controls for this Metacard. */
  public static final String OTHER_DISSEMINATION_CONTROLS = "security.other-dissemination-controls";

  /** Attribute name for accessing the country codes of owners and producers for this Metacard. */
  public static final String OWNER_PRODUCER = "security.owner-producer";

  /** Attribute name for accessing the releasability for this Metacard. */
  public static final String RELEASABILITY = "security.releasability";

  /*  The following attribute names are experimental and may change. */

  /** Attribute name for accessing the metadata originator classification for this Metacard. */
  public static final String METADATA_ORIGINATOR_CLASSIFICATION =
      "ext.metadata-originator-classification";

  /** Attribute name for accessing the metadata classification for this Metacard. */
  public static final String METADATA_CLASSIFICATION = "ext.metadata-classification";

  /**
   * Attribute name for accessing the security classification system for the metadata for this
   * Metacard.
   */
  public static final String METADATA_CLASSIFICATION_SYSTEM = "ext.metadata-classification-system";

  /** Attribute name for accessing the metadata dissemination controls for this Metacard. */
  public static final String METADATA_DISSEMINATION = "ext.metadata-dissemination-controls";

  /** Attribute name for accessing the metadata releasability for this Metacard. */
  public static final String METADATA_RELEASABILITY = "ext.metadata-releasability";

  /** Attribute name for accessing the resource originator classification for this Metacard. */
  public static final String RESOURCE_ORIGINATOR_CLASSIFICATION =
      "ext.resource-originator-classification";

  /** Attribute name for accessing the resource classification for this Metacard. */
  public static final String RESOURCE_CLASSIFICATION = "ext.resource-classification";

  /**
   * Attribute name for accessing the security classification system for the resource for this
   * Metacard.
   */
  public static final String RESOURCE_CLASSIFICATION_SYSTEM = "ext.resource-classification-system";

  /** Attribute name for accessing the resource releasability for this Metacard. */
  public static final String RESOURCE_RELEASABILITY = "ext.resource-releasability";

  /** Attribute name for accessing the resource dissemination controls for this Metacard. */
  public static final String RESOURCE_DISSEMINATION = "ext.resource-dissemination-controls";
}
