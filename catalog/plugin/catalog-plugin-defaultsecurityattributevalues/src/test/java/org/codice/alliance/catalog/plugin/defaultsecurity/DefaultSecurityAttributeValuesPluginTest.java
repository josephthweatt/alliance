/**
 * Copyright (c) Codice Foundation
 * <p>
 * This is free software: you can redistribute it and/or modify it under the terms of the GNU Lesser
 * General Public License as published by the Free Software Foundation, either version 3 of the
 * License, or any later version.
 * <p>
 * This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
 * even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details. A copy of the GNU Lesser General Public License
 * is distributed along with this program and can be found at
 * <http://www.gnu.org/licenses/lgpl.html>.
 */
package org.codice.alliance.catalog.plugin.defaultsecurity;

import static org.codice.alliance.catalog.plugin.defaultsecurity.DefaultSecurityAttributeValuesPlugin.CLASSIFICATION_KEY;
import static org.codice.alliance.catalog.plugin.defaultsecurity.DefaultSecurityAttributeValuesPlugin.CODEWORDS_KEY;
import static org.codice.alliance.catalog.plugin.defaultsecurity.DefaultSecurityAttributeValuesPlugin.DISSEMINATION_CONTROLS_KEY;
import static org.codice.alliance.catalog.plugin.defaultsecurity.DefaultSecurityAttributeValuesPlugin.OTHER_DISSEMINATION_CONTROLS_KEY;
import static org.codice.alliance.catalog.plugin.defaultsecurity.DefaultSecurityAttributeValuesPlugin.OWNER_PRODUCER_KEY;
import static org.codice.alliance.catalog.plugin.defaultsecurity.DefaultSecurityAttributeValuesPlugin.RELEASABILITY_KEY;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.is;
import static org.hamcrest.Matchers.not;
import static org.mockito.Matchers.any;
import static org.mockito.Matchers.anyObject;
import static org.mockito.Matchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;
import static org.mockito.MockitoAnnotations.initMocks;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.apache.shiro.subject.PrincipalCollection;
import org.codice.alliance.catalog.core.api.impl.types.SecurityAttributes;
import org.codice.alliance.catalog.core.api.types.Security;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.opensaml.core.xml.schema.XSString;
import org.opensaml.saml.saml2.core.AttributeStatement;
import org.osgi.service.cm.ConfigurationAdmin;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;

import ddf.catalog.data.Attribute;
import ddf.catalog.data.AttributeDescriptor;
import ddf.catalog.data.Metacard;
import ddf.catalog.data.MetacardType;
import ddf.catalog.data.Result;
import ddf.catalog.data.impl.AttributeImpl;
import ddf.catalog.data.impl.MetacardImpl;
import ddf.catalog.operation.CreateRequest;
import ddf.catalog.operation.UpdateRequest;
import ddf.catalog.operation.impl.CreateRequestImpl;
import ddf.security.Subject;
import ddf.security.assertion.SecurityAssertion;

public class DefaultSecurityAttributeValuesPluginTest {

    public static final String USER_ATTRIB_1 = "UserAttrib1";

    public static final String USER_ATTRIB_2 = "UserAttrib2";

    public static final String CLASSIFICATION_ATTRIB_VAL = "1";

    public static final String CODEWORD_ATTRIB_VAL = "2";

    private DefaultSecurityAttributeValuesPlugin defaultSecurityAttributeValuesPlugin;

    @Mock
    private Metacard unmarkedMetacard;

    @Mock
    private Metacard markedMetacard;

    @Mock
    private Result unmarkedResult;

    @Mock
    private Result markedResult;

    @Mock
    private Attribute emptySecurityAttributeList;

    @Mock
    private Attribute securityAttributeList;

    @Mock
    private HashMap<String, Object> mockedEmptyAttributeMap;

    @Mock
    private HashMap<String, Object> mockedFilledAttributeMap;

    @Mock
    private Subject mockedSubject;

    @Mock
    private ConfigurationAdmin configurationAdmin;

    @Mock
    private PrincipalCollection mockedPrincipalCollection;

    @Mock
    private SecurityAssertion mockedAssertion;

    @Mock
    private AttributeStatement mockedAttributeStatement1;

    @Mock
    private org.opensaml.saml.saml2.core.Attribute mockedAttribute1;

    @Mock
    private AttributeStatement mockedAttributeStatement2;

    @Mock
    private org.opensaml.saml.saml2.core.Attribute mockedAttribute2;

    @Mock
    private XSString mockedXss1;

    @Mock
    private XSString mockedXss2;

    @Mock
    private MetacardType metacardType;

    @Mock
    private AttributeDescriptor attributeDescriptor;

    @Mock
    private CreateRequest createRequest;

    @Mock
    private UpdateRequest updateRequest;

    @Before
    public void setup() {
        initMocks(this);

        when(mockedSubject.getPrincipals()).thenReturn(mockedPrincipalCollection);
        when(mockedPrincipalCollection.oneByType(anyObject())).thenReturn(mockedAssertion);
        when(mockedAssertion.getAttributeStatements()).thenReturn(Arrays.asList(
                mockedAttributeStatement1,
                mockedAttributeStatement2));

        when(mockedAttributeStatement1.getAttributes()).thenReturn(Arrays.asList(mockedAttribute1));
        when(mockedAttributeStatement2.getAttributes()).thenReturn(Arrays.asList(mockedAttribute2));
        when(mockedXss1.getValue()).thenReturn(CLASSIFICATION_ATTRIB_VAL);
        when(mockedXss2.getValue()).thenReturn(CODEWORD_ATTRIB_VAL);
        when(mockedAttribute1.getAttributeValues()).thenReturn(Arrays.asList(mockedXss1));
        when(mockedAttribute2.getAttributeValues()).thenReturn(Arrays.asList(mockedXss2));
        when(mockedAttribute1.getName()).thenReturn(USER_ATTRIB_1);
        when(mockedAttribute2.getName()).thenReturn(USER_ATTRIB_2);

        defaultSecurityAttributeValuesPlugin =
                new DefaultSecurityAttributeValuesPlugin(new SecurityAttributes(),
                        ImmutableMap.of(CLASSIFICATION_KEY,
                                USER_ATTRIB_1,
                                CODEWORDS_KEY,
                                USER_ATTRIB_2),
                        () -> mockedSubject);

        when(markedMetacard.getAttribute(eq(Metacard.SECURITY))).thenReturn(securityAttributeList);
        when(unmarkedMetacard.getAttribute(eq(Metacard.SECURITY))).thenReturn(securityAttributeList);
        when(securityAttributeList.getValue()).thenReturn((Serializable) Collections.EMPTY_MAP);
        when(unmarkedMetacard.getMetacardType()).thenReturn(metacardType);
        when(metacardType.getAttributeDescriptor(any(String.class))).thenReturn(attributeDescriptor);

        when(createRequest.getMetacards()).thenReturn(Collections.singletonList(unmarkedMetacard));
        when(updateRequest.getUpdates()).thenReturn(Collections.singletonList(Maps.immutableEntry(
                "key",
                unmarkedMetacard)));

        when(unmarkedMetacard.getMetacardType()).thenReturn(metacardType);
        when(markedMetacard.getMetacardType()).thenReturn(metacardType);
        when(emptySecurityAttributeList.getValue()).thenReturn(mockedEmptyAttributeMap);
        when(mockedEmptyAttributeMap.isEmpty()).thenReturn(true);
    }

    @Test
    public void testProcessUnmarkedMetacard() throws Exception {
        Metacard modifiedMetacard = defaultSecurityAttributeValuesPlugin.addDefaults(
                unmarkedMetacard);
        assertThat(unmarkedMetacard, not(modifiedMetacard));
        assertThat(CODEWORD_ATTRIB_VAL,
                is(modifiedMetacard.getAttribute(Security.CODEWORDS)
                        .getValue()));
        assertThat(CLASSIFICATION_ATTRIB_VAL,
                is(modifiedMetacard.getAttribute(Security.CLASSIFICATION)
                        .getValue()));
        assertThat(modifiedMetacard.getTags(),
                contains(DefaultSecurityAttributeValuesPlugin.DEFAULTMARKINGS));
    }

    @Test
    public void testProcessUnmarkedMetacardWtihSecurityAttributeDescriptors() throws Exception {
        Set<AttributeDescriptor> attributeDescriptors = mock(Set.class);
        when(metacardType.getAttributeDescriptors()).thenReturn(attributeDescriptors);
        when(attributeDescriptors.contains(any(AttributeDescriptor.class))).thenReturn(true);

        Metacard modifiedMetacard = defaultSecurityAttributeValuesPlugin.addDefaults(
                unmarkedMetacard);

        assertThat(unmarkedMetacard, not(modifiedMetacard));
        verify(unmarkedMetacard, times(3)).setAttribute(any(Attribute.class));
    }

    @Test
    public void testProcessMarkedMetacardWithClassification() throws Exception {
        when(markedMetacard.getAttribute(eq(Security.CLASSIFICATION))).thenReturn(new AttributeImpl(
                Security.CLASSIFICATION,
                CLASSIFICATION_ATTRIB_VAL));
        verifyProcessingOfMarkedMetacard();
    }

    @Test
    public void testProcessMarkedMetacardWithCodeWords() throws Exception {
        when(markedMetacard.getAttribute(eq(Security.CODEWORDS))).thenReturn(new AttributeImpl(
                Security.CODEWORDS,
                CODEWORD_ATTRIB_VAL));
        verifyProcessingOfMarkedMetacard();
    }

    @Test
    public void testProcessCreateRequest() throws Exception {
        CreateRequest modifiedRequest = defaultSecurityAttributeValuesPlugin.process(createRequest);
        assertThat(createRequest, not(modifiedRequest));
    }

    @Test
    public void testProcessUpdateRequest() throws Exception {
        UpdateRequest modifiedRequest = defaultSecurityAttributeValuesPlugin.process(updateRequest);
        assertThat(updateRequest, is(modifiedRequest));
    }

    @Test
    public void testComponentManagedUpdateStrategy() throws Exception {

        Map<String, Object> updateMap = new HashMap<>();

        updateMap.put(CLASSIFICATION_KEY, USER_ATTRIB_1);
        updateMap.put(CODEWORDS_KEY, USER_ATTRIB_2);
        updateMap.put(RELEASABILITY_KEY, USER_ATTRIB_1);
        updateMap.put(OWNER_PRODUCER_KEY, USER_ATTRIB_2);
        updateMap.put(DISSEMINATION_CONTROLS_KEY, USER_ATTRIB_1);
        updateMap.put(OTHER_DISSEMINATION_CONTROLS_KEY, USER_ATTRIB_2);

        defaultSecurityAttributeValuesPlugin.update(updateMap);

        MetacardImpl inputMetacard = new MetacardImpl();
        CreateRequestImpl preCreateRequest = new CreateRequestImpl(inputMetacard);
        CreateRequest postCreateRequest = defaultSecurityAttributeValuesPlugin.process(
                preCreateRequest);
        Metacard outputMetacard = postCreateRequest.getMetacards()
                .get(0);

        assertThat(outputMetacard.getAttribute(Security.CLASSIFICATION)
                .getValue(), is("1"));
        assertThat(outputMetacard.getAttribute(Security.CODEWORDS)
                .getValue(), is("2"));
        assertThat(outputMetacard.getAttribute(Security.RELEASABILITY)
                .getValue(), is("1"));
        assertThat(outputMetacard.getAttribute(Security.OWNER_PRODUCER)
                .getValue(), is("2"));
        assertThat(outputMetacard.getAttribute(Security.DISSEMINATION_CONTROLS)
                .getValue(), is("1"));
        assertThat(outputMetacard.getAttribute(Security.OTHER_DISSEMINATION_CONTROLS)
                .getValue(), is("2"));
    }

    private void verifyProcessingOfMarkedMetacard() throws Exception {
        when(securityAttributeList.getValue()).thenReturn((Serializable) Collections.emptyMap());

        Metacard modifiedMetacard =
                defaultSecurityAttributeValuesPlugin.addDefaults(markedMetacard);

        verify(markedMetacard, times(0)).setAttribute(any(AttributeImpl.class));
        assertThat(markedMetacard, is(modifiedMetacard));
    }
}