/*******************************************************************************
 * Copyright (c) 2022 Eclipse RDF4J contributors.
 *  All rights reserved. This program and the accompanying materials
 *  are made available under the terms of the Eclipse Distribution License v1.0
 *  which accompanies this distribution, and is available at
 *  http://www.eclipse.org/org/documents/edl-v10.php.
 ******************************************************************************/

package org.eclipse.rdf4j.sail.shacl.ast;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import org.eclipse.rdf4j.model.Model;
import org.eclipse.rdf4j.model.Resource;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.impl.DynamicModel;
import org.eclipse.rdf4j.model.impl.DynamicModelFactory;

public class ContextWithShapes {

	private final Resource[] contexts;
	private final List<Shape> shapes;

	public ContextWithShapes(Resource[] contexts, List<Shape> shapes) {
		this.contexts = contexts;
		this.shapes = shapes;
	}

	public Resource[] getContexts() {
		return contexts;
	}

	public List<Shape> getShapes() {
		return shapes;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) {
			return true;
		}
		if (o == null || getClass() != o.getClass()) {
			return false;
		}
		ContextWithShapes that = (ContextWithShapes) o;
		return Arrays.equals(contexts, that.contexts) && shapes.equals(that.shapes);
	}

	@Override
	public int hashCode() {
		int result = Objects.hash(shapes);
		result = 31 * result + Arrays.hashCode(contexts);
		return result;
	}

	public void toModel(Model model) {
		DynamicModel emptyModel = new DynamicModelFactory().createEmptyModel();
		for (Shape shape : shapes) {
			shape.toModel(emptyModel);
		}
		for (Statement statement : emptyModel) {
			for (Resource context : contexts) {
				model.add(statement.getSubject(), statement.getPredicate(), statement.getObject(), context);
			}
		}
	}
}
