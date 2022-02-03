/*******************************************************************************
 * Copyright (c) 2022 Eclipse RDF4J contributors.
 *  All rights reserved. This program and the accompanying materials
 *  are made available under the terms of the Eclipse Distribution License v1.0
 *  which accompanies this distribution, and is available at
 *  http://www.eclipse.org/org/documents/edl-v10.php.
 ******************************************************************************/

package org.eclipse.rdf4j.sail.shacl.wrapper.shape;

import java.util.stream.Stream;

import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Resource;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.vocabulary.RDF;
import org.eclipse.rdf4j.sail.SailConnection;

public class BackwardChainingShapeSource implements ShapeSource {

	private final SailConnection sailConnection;
	private final Resource[] context;

	public BackwardChainingShapeSource(SailConnection sailConnection) {
		this(sailConnection, null);
	}

	private BackwardChainingShapeSource(SailConnection sailConnection, Resource[] context) {
		this.sailConnection = sailConnection;
		this.context = context;
	}

	public BackwardChainingShapeSource withContext(Resource[] context) {
		return new BackwardChainingShapeSource(sailConnection, context);
	}

	public Stream<Resource> getAllShapeContexts() {
		assert context == null;
		return Stream
				.of(getContext(Predicates.TARGET_NODE), getContext(Predicates.TARGET_CLASS),
						getContext(Predicates.TARGET_SUBJECTS_OF), getContext(Predicates.TARGET_OBJECTS_OF),
						getContext(Predicates.TARGET_PROP), getContext(Predicates.RSX_targetShape))
				.reduce(Stream::concat)
				.get()
				.distinct();
	}

	private Stream<Resource> getContext(Predicates predicate) {
		assert context == null;

		return sailConnection.getStatements(null, predicate.getIRI(), null, true)
				.stream()
				.map(Statement::getContext)
				.distinct();
	}

	public Stream<Resource> getTargetableShape() {
		assert context != null;
		return Stream
				.of(getSubjects(Predicates.TARGET_NODE), getSubjects(Predicates.TARGET_CLASS),
						getSubjects(Predicates.TARGET_SUBJECTS_OF), getSubjects(Predicates.TARGET_OBJECTS_OF),
						getSubjects(Predicates.TARGET_PROP), getSubjects(Predicates.RSX_targetShape))
				.reduce(Stream::concat)
				.get()
				.distinct();
	}

	public boolean isType(Resource subject, IRI type) {
		assert context != null;
		return sailConnection.hasStatement(subject, RDF.TYPE, type, true, context);
	}

	public Stream<Resource> getSubjects(Predicates predicate) {
		assert context != null;

		return sailConnection.getStatements(null, predicate.getIRI(), null, true, context)
				.stream()
				.map(Statement::getSubject)
				.distinct();

	}

	public Stream<Value> getObjects(Resource subject, Predicates predicate) {
		assert context != null;

		return sailConnection.getStatements(subject, predicate.getIRI(), null, true, context)
				.stream()
				.map(Statement::getObject)
				.distinct();
	}

	public Stream<Statement> getAllStatements(Resource id) {
		assert context != null;
		return sailConnection.getStatements(id, null, null, true, context).stream().map(s -> ((Statement) s));
	}

	public Value getRdfFirst(Resource subject) {
		assert context != null;

		return sailConnection.getStatements(subject, RDF.FIRST, null, true, context)
				.stream()
				.map(Statement::getObject)
				.findAny()
				.orElse(null);
		// .orElseThrow(() -> new IllegalStateException("Corrupt rdf:list at rdf:first: " + subject));
	}

	public Resource getRdfRest(Resource subject) {
		assert context != null;

		Value value = sailConnection.getStatements(subject, RDF.REST, null, true, context)
				.stream()
				.map(Statement::getObject)
				.findAny()
				.orElse(null);
		// .orElseThrow(() -> new IllegalStateException("Corrupt rdf:list at rdf:rest: " + subject));

		return ((Resource) value);
	}

}
