/*******************************************************************************
 * Copyright (c) 2022 Eclipse RDF4J contributors.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Distribution License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/org/documents/edl-v10.php.
 ******************************************************************************/

package org.eclipse.rdf4j.sail.shacl;

import org.eclipse.rdf4j.common.annotation.InternalUseOnly;
import org.eclipse.rdf4j.model.Resource;

@InternalUseOnly
public class ValidationSettings {

	private final Resource[] dataGraph;
	private final boolean logValidationPlans;
	private final boolean validateEntireBaseSail;

	public ValidationSettings(Resource[] dataGraph, boolean logValidationPlans, boolean validateEntireBaseSail) {

		this.dataGraph = dataGraph;
		this.logValidationPlans = logValidationPlans;
		this.validateEntireBaseSail = validateEntireBaseSail;
	}

	public ValidationSettings() {
		dataGraph = new Resource[] { null };
		logValidationPlans = false;
		validateEntireBaseSail = false;
	}

	public Resource[] getDataGraph() {
		return dataGraph;
	}

	public boolean isLogValidationPlans() {
		return logValidationPlans;
	}

	public boolean isValidateEntireBaseSail() {
		return validateEntireBaseSail;
	}
}
