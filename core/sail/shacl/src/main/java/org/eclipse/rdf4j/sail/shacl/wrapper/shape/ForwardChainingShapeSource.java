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
import org.eclipse.rdf4j.model.vocabulary.RSX;
import org.eclipse.rdf4j.model.vocabulary.SHACL;
import org.eclipse.rdf4j.repository.sail.SailRepositoryConnection;
import org.eclipse.rdf4j.sail.SailConnection;

public class ForwardChainingShapeSource implements ShapeSource {

	private final SailRepositoryConnection shapesRepoWithReasoningConnection;
	private final Resource[] context;

	public ForwardChainingShapeSource(SailRepositoryConnection shapesRepoWithReasoningConnection) {
		this(shapesRepoWithReasoningConnection, null);
	}

	private ForwardChainingShapeSource(SailRepositoryConnection shapesRepoWithReasoningConnection,
			Resource[] context) {
		this.shapesRepoWithReasoningConnection = shapesRepoWithReasoningConnection;
		this.context = context;
	}

	public ForwardChainingShapeSource withContext(Resource[] context) {
		return new ForwardChainingShapeSource(shapesRepoWithReasoningConnection, context);
	}

	public Stream<Resource> getAllShapeContexts() {
		assert context == null;
		return Stream
				.of(getContext(Predicates.TARGET_NODE),
						getContext(Predicates.TARGET_CLASS),
						getContext(Predicates.TARGET_SUBJECTS_OF),
						getContext(Predicates.TARGET_OBJECTS_OF),
						getContext(Predicates.TARGET_PROP),
						getContext(Predicates.RSX_targetShape)
				)
				.reduce(Stream::concat)
				.get()
				.distinct();
	}

	private Stream<Resource> getContext(Predicates predicate) {
		assert context == null;

		return shapesRepoWithReasoningConnection.getStatements(null, predicate.getIRI(), null, true)
				.stream()
				.map(Statement::getContext)
				.distinct();
	}

	public Stream<Resource> getTargetableShape() {
		assert context != null;
		return Stream
				.of(getSubjects(Predicates.TARGET_NODE),
						getSubjects(Predicates.TARGET_CLASS),
						getSubjects(Predicates.TARGET_SUBJECTS_OF),
						getSubjects(Predicates.TARGET_OBJECTS_OF),
						getSubjects(Predicates.TARGET_PROP),
						getSubjects(Predicates.RSX_targetShape)
				)
				.reduce(Stream::concat)
				.get()
				.distinct();
	}

	public boolean isType(Resource subject, IRI type) {
		assert context != null;
		return shapesRepoWithReasoningConnection.hasStatement(subject, RDF.TYPE, type, true, context);
	}

	public Stream<Resource> getSubjects(Predicates predicate) {
		assert context != null;

		return shapesRepoWithReasoningConnection.getStatements(null, predicate.getIRI(), null, true, context)
				.stream()
				.map(Statement::getSubject)
				.distinct();

	}

	public Stream<Value> getObjects(Resource subject, Predicates predicate) {
		assert context != null;

		return shapesRepoWithReasoningConnection.getStatements(subject, predicate.getIRI(), null, true, context)
				.stream()
				.map(Statement::getObject)
				.distinct();
	}

	public Stream<Statement> getAllStatements(Resource id) {
		assert context != null;
		return shapesRepoWithReasoningConnection.getStatements(id, null, null, true, context)
				.stream()
				.map(s -> ((Statement) s));
	}

	public Value getRdfFirst(Resource subject) {
		assert context != null;

		return shapesRepoWithReasoningConnection.getStatements(subject, RDF.FIRST, null, true, context)
				.stream()
				.map(Statement::getObject)
				.findAny()
				.orElse(null);
		// .orElseThrow(() -> new IllegalStateException("Corrupt rdf:list at rdf:first: " + subject));
	}

	public Resource getRdfRest(Resource subject) {
		assert context != null;

		return (Resource) shapesRepoWithReasoningConnection.getStatements(subject, RDF.REST, null, true, context)
				.stream()
				.map(Statement::getObject)
				.findAny()
				.orElse(null);
		// .orElseThrow(() -> new IllegalStateException("Corrupt rdf:list at rdf:rest: " + subject));

//		if (value.isResource()) {
//			return ((Resource) value);
//		} else {
//			throw new IllegalStateException("Corrupt rdf:list at rdf:rest: " + subject);
//		}

	}

}
