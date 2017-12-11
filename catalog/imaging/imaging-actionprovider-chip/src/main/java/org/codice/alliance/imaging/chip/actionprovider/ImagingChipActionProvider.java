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
package org.codice.alliance.imaging.chip.actionprovider;

import com.vividsolutions.jts.geom.GeometryFactory;
import com.vividsolutions.jts.io.ParseException;
import com.vividsolutions.jts.io.WKTReader;
import ddf.action.Action;
import ddf.action.MultiActionProvider;
import ddf.action.impl.ActionImpl;
import ddf.catalog.content.data.ContentItem;
import ddf.catalog.data.Attribute;
import ddf.catalog.data.Metacard;
import java.io.Serializable;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.apache.commons.lang3.StringUtils;
import org.apache.http.client.utils.URLEncodedUtils;
import org.codice.ddf.configuration.SystemBaseUrl;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ImagingChipActionProvider implements MultiActionProvider {

  static final String TITLE = "Chip Image";

  static final String DESCRIPTION =
      "Opens a new window to enter the boundaries of an image chip for a Metacard.";

  private static final String PATH = "/chipping/chipping.html";

  static final String ID = "catalog.data.metacard.image.chipping";

  private static final Logger LOGGER = LoggerFactory.getLogger(ImagingChipActionProvider.class);

  static final String NITF_IMAGE_METACARD_TYPE = "isr.image";

  private static final String ORIGINAL_QUALIFIER = "original";

  private static final String QUALIFIER_KEY = "qualifier";

  private static final Pattern ALLIANCE_DOWNLOAD_RESOURCE_PATH_PATTERN =
      Pattern.compile("/.*/catalog/sources/.*/.*");

  private final GeometryFactory geometryFactory = new GeometryFactory();

  @Override
  public <T> List<Action> getActions(T subject) {
    // canHandle has already been checked at this point, so no need to verify subject
    final Metacard metacard = (Metacard) subject;

    return getChippingUrl(metacard)
        .map(
            url ->
                Collections.singletonList(
                    (Action) new ActionImpl(getId(), TITLE, DESCRIPTION, url)))
        .orElseGet(Collections::emptyList);
  }

  private static Optional<URL> getChippingUrl(Metacard metacard) {
    // canHandle has already been checked at this point, so no need to verify isPresent
    final URI derivedResourceUri = getOriginalDerivedResourceUri(metacard).get();
    if (canBeChippedLocally(derivedResourceUri)) {
      final String defaultChippingUrlString =
          String.format(
              "%s%s?id=%s&source=%s",
              SystemBaseUrl.getBaseUrl(), PATH, metacard.getId(), metacard.getSourceId());
      try {
        return Optional.of(new URL(defaultChippingUrlString));
      } catch (MalformedURLException e) {
        // This should never happen.
      }
    } else {
      // If the resource.derived-uri attribute value matches the usual Alliance download URL format
      // ("[protocol]://[host]:[port]/[services name]/catalog/sources/[source id]/[metacard
      // id]?transform=resource&qualifier=[original or overview]"), assume that there is a
      // chipping URL that can be constructed from the scheme, host, port, source, and id of
      // the value. This allows the {@value TITLE} Action to link directly to the remote
      // system if the derived resource is from another Alliance instance.
      try {
        final URL derivedResourceUrl = derivedResourceUri.toURL();

        final String host = derivedResourceUrl.getHost(); // {@code null} if the host is undefined
        final int port = derivedResourceUrl.getPort(); // -1 if the port is not set
        final String path = derivedResourceUrl.getPath(); // an empty string if one does not exist
        final String query =
            derivedResourceUrl.getQuery(); // <CODE>null</CODE> if one does not exist
        final String expectedQuery =
            String.format("transform=resource&qualifier=%s", ORIGINAL_QUALIFIER);
        if (!StringUtils.isEmpty(host)
            && port != -1
            && ALLIANCE_DOWNLOAD_RESOURCE_PATH_PATTERN.matcher(path).matches()
            && StringUtils.equals(query, expectedQuery)) {
          final String[] paths = path.split("/");
          final String source = paths[4];
          final String id = paths[5];

          final String chippingPathString = String.format("%s?id=%s&source=%s", PATH, id, source);
          try {
            return Optional.of(
                new URL(derivedResourceUrl.getProtocol(), host, port, chippingPathString));
          } catch (MalformedURLException e) {
            // This should probably never happen because the parts used to construct the URL have
            // been validated.
          }
        } else {
          // Unable to construct a remote chipping URL because the original resource.derived-uri
          // does not match the known Alliance format.
        }
      } catch (MalformedURLException e) {
        // Unable to cast derivedResourceUri to a URL, which means that the resource still may be
        // able to be chipped locally but is not yet supported by the canBeChippedLocally method.
      }
    }

    LOGGER.debug(
        "Unable to construct a chipping URL for NITF image metacard id={}, source id={}, resource-uri={}. Not displaying the Chip Image Action.",
        metacard.getId(),
        metacard.getResourceURI(),
        metacard.getSourceId());
    return Optional.empty();
  }

  @Override
  public String getId() {
    return ID;
  }

  @Override
  public <T> boolean canHandle(T subject) {
    if (subject instanceof Metacard) {
      final Metacard metacard = (Metacard) subject;

      final boolean isImageNitf =
          NITF_IMAGE_METACARD_TYPE.equals(metacard.getMetacardType().getName());
      final boolean hasLocation = hasValidLocation(metacard.getLocation());
      // The chipping transformer requires the NITF resource, the overview derived image
      // resource, and the original derived image resource.
      final boolean hasNitfResource = metacard.getResourceURI() != null;
      boolean hasOriginalDerivedImageResource = getOriginalDerivedResourceUri(metacard).isPresent();
      // assume that if there is an original, there is also an overview
      boolean hasOverviewDerivedImageResource = hasOriginalDerivedImageResource;

      return isImageNitf
          && hasLocation
          && hasNitfResource
          && hasOverviewDerivedImageResource
          && hasOriginalDerivedImageResource;
    } else {
      return false;
    }
  }

  private boolean hasValidLocation(String location) {
    if (StringUtils.isNotBlank(location)) {
      try {
        // parse the WKT location to determine if it has valid format
        final WKTReader wktReader = new WKTReader(geometryFactory);
        wktReader.read(location);
        return true;
      } catch (ParseException e) {
        LOGGER.debug("Location [{}] is invalid. Cannot chip this image", location);
      }
    }

    return false;
  }

  private static Optional<URI> getOriginalDerivedResourceUri(final Metacard metacard) {
    Optional<URI> optional = Optional.empty();
    final Attribute derivedResourceUriAttribute =
        metacard.getAttribute(Metacard.DERIVED_RESOURCE_URI);

    if (derivedResourceUriAttribute == null) {
      return optional;
    }

    for (Serializable value : getStringAttributes(derivedResourceUriAttribute)) {
      final String derivedResourceUriString = (String) value;
      try {
        final URI derivedResourceUri = new URI(derivedResourceUriString);

        if (canBeChippedLocally(derivedResourceUri)
                && StringUtils.equals(ORIGINAL_QUALIFIER, derivedResourceUri.getFragment())
            || URLEncodedUtils.parse(derivedResourceUri, StandardCharsets.UTF_8.name())
                .stream()
                .anyMatch(
                    parameter ->
                        QUALIFIER_KEY.equals(parameter.getName())
                            && StringUtils.equals(ORIGINAL_QUALIFIER, parameter.getValue()))) {
          optional = Optional.of(derivedResourceUri);
          break;
        }
      } catch (URISyntaxException e) {
        // ignore
      }
    }

    return optional;
  }

  /**
   * Assume that the "content" scheme in the resource.derived-uri indicates that the resource can be
   * chipped locally.
   */
  private static boolean canBeChippedLocally(URI derivedResourceUri) {
    return StringUtils.equals(ContentItem.CONTENT_SCHEME, derivedResourceUri.getScheme());
  }

  private static List<Serializable> getStringAttributes(Attribute derivedResourceUriAttribute) {
    return derivedResourceUriAttribute
        .getValues()
        .stream()
        .filter(v -> v instanceof String)
        .collect(Collectors.toList());
  }
}
