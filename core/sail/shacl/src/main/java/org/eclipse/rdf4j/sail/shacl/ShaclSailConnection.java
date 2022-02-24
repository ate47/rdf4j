/*******************************************************************************
 * Copyright (c) 2018 Eclipse RDF4J contributors.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Distribution License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/org/documents/edl-v10.php.
 *******************************************************************************/

package org.eclipse.rdf4j.sail.shacl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.rdf4j.common.concurrent.locks.Lock;
import org.eclipse.rdf4j.common.concurrent.locks.StampedLockManager;
import org.eclipse.rdf4j.common.iteration.CloseableIteration;
import org.eclipse.rdf4j.common.transaction.IsolationLevel;
import org.eclipse.rdf4j.common.transaction.IsolationLevels;
import org.eclipse.rdf4j.common.transaction.TransactionSetting;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Resource;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.vocabulary.RDF4J;
import org.eclipse.rdf4j.repository.sail.SailRepositoryConnection;
import org.eclipse.rdf4j.sail.NotifyingSailConnection;
import org.eclipse.rdf4j.sail.Sail;
import org.eclipse.rdf4j.sail.SailConnection;
import org.eclipse.rdf4j.sail.SailConnectionListener;
import org.eclipse.rdf4j.sail.SailException;
import org.eclipse.rdf4j.sail.UpdateContext;
import org.eclipse.rdf4j.sail.helpers.NotifyingSailConnectionWrapper;
import org.eclipse.rdf4j.sail.memory.MemoryStore;
import org.eclipse.rdf4j.sail.shacl.ShaclSail.TransactionSettings.ValidationApproach;
import org.eclipse.rdf4j.sail.shacl.ast.ContextWithShapes;
import org.eclipse.rdf4j.sail.shacl.ast.Shape;
import org.eclipse.rdf4j.sail.shacl.ast.planNodes.EmptyNode;
import org.eclipse.rdf4j.sail.shacl.ast.planNodes.PlanNode;
import org.eclipse.rdf4j.sail.shacl.ast.planNodes.SingleCloseablePlanNode;
import org.eclipse.rdf4j.sail.shacl.ast.planNodes.ValidationExecutionLogger;
import org.eclipse.rdf4j.sail.shacl.ast.planNodes.ValidationTuple;
import org.eclipse.rdf4j.sail.shacl.results.ValidationReport;
import org.eclipse.rdf4j.sail.shacl.results.lazy.LazyValidationReport;
import org.eclipse.rdf4j.sail.shacl.results.lazy.ValidationResultIterator;
import org.eclipse.rdf4j.sail.shacl.wrapper.data.ConnectionsGroup;
import org.eclipse.rdf4j.sail.shacl.wrapper.data.RdfsSubClassOfReasoner;
import org.eclipse.rdf4j.sail.shacl.wrapper.data.VerySimpleRdfsBackwardsChainingConnection;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Heshan Jayasinghe
 * @author Håvard Ottestad
 */
public class ShaclSailConnection extends NotifyingSailConnectionWrapper implements SailConnectionListener {

	private static final Logger logger = LoggerFactory.getLogger(ShaclSailConnection.class);

	private final SailConnection previousStateConnection;
	private final SailConnection serializableConnection;
	private final SailConnection previousStateSerializableConnection;

	private final boolean useDefaultShapesGraph;
	private final IRI[] shapesGraphs;

	Sail addedStatements;
	Sail removedStatements;

	private final HashSet<Statement> addedStatementsSet = new HashSet<>();
	private final HashSet<Statement> removedStatementsSet = new HashSet<>();

	private boolean shapeRefreshNeeded = false;
	private boolean shapesModifiedInCurrentTransaction = false;

	public final ShaclSail sail;

	private Stats stats;

	RdfsSubClassOfReasoner rdfsSubClassOfReasoner;

	private boolean preparedHasRun = false;

	private Lock writeLock;
	private Lock readLock;

	private StampedLockManager.Cache<List<ContextWithShapes>>.WritableState writableShapesCache;
	private StampedLockManager.Cache<List<ContextWithShapes>>.ReadableState readableShapesCache;

	private final SailRepositoryConnection shapesRepoConnection;

	// used to determine if we are currently registered as a connection listener (getting added/removed notifications)
	private boolean connectionListenerActive = false;

	private IsolationLevel currentIsolationLevel = null;

	private Settings transactionSettings;
	private TransactionSetting[] transactionSettingsRaw = new TransactionSetting[0];

	ShaclSailConnection(ShaclSail sail, NotifyingSailConnection connection,
			SailConnection previousStateConnection, SailConnection serializableConnection,
			SailConnection previousStateSerializableConnection,
			SailRepositoryConnection shapesRepoConnection) {
		super(connection);
		this.previousStateConnection = previousStateConnection;
		this.serializableConnection = serializableConnection;
		this.previousStateSerializableConnection = previousStateSerializableConnection;
		this.shapesRepoConnection = shapesRepoConnection;
		this.sail = sail;
		this.transactionSettings = getDefaultSettings(sail);
		this.useDefaultShapesGraph = sail.getShapesGraphs().contains(RDF4J.SHACL_SHAPE_GRAPH);
		this.shapesGraphs = sail.getShapesGraphs().stream().map(g -> {
			if (g.equals(RDF4J.NIL)) {
				return null;
			}
			return g;
		}).toArray(IRI[]::new);
	}

	private Settings getDefaultSettings(ShaclSail sail) {
		return new Settings(sail.isCacheSelectNodes(), sail.isValidationEnabled(), sail.isParallelValidation(),
				currentIsolationLevel);
	}

	@Override
	public void setTransactionSettings(TransactionSetting... settings) {
		super.setTransactionSettings(settings);
		this.transactionSettingsRaw = settings;
	}

	@Override
	public void begin() throws SailException {
		begin(sail.getDefaultIsolationLevel());
	}

	@Override
	public void begin(IsolationLevel level) throws SailException {

		currentIsolationLevel = level;

		assert addedStatements == null;
		assert removedStatements == null;
		assert readableShapesCache == null;
		assert writableShapesCache == null;
		assert readLock == null;
		assert writeLock == null;

		stats = new Stats();

		// start two transactions, synchronize on underlying sail so that we get two transactions immediately
		// successively
		synchronized (sail) {
			super.begin(level);
			hasStatement(null, null, null, false); // actually force a transaction to start
			shapesRepoConnection.begin(currentIsolationLevel);
			previousStateConnection.begin(currentIsolationLevel);
			previousStateConnection.hasStatement(null, null, null, false); // actually force a transaction to start
		}

		stats.setEmptyBeforeTransaction(isEmpty());

		transactionSettings = getDefaultSettings(sail);

		if (stats.wasEmptyBeforeTransaction() && !shouldUseSerializableValidation()) {
			transactionSettings.switchToBulkValidation();
		}

		transactionSettings.applyTransactionSettings(getLocalTransactionSettings());

		assert transactionSettings.parallelValidation != null;
		assert transactionSettings.cacheSelectedNodes != null;
		assert transactionSettings.validationApproach != null;

		if (isBulkValidation() || !isValidationEnabled()) {
			removeConnectionListener(this);
		} else {
			addConnectionListener(this);
		}

	}

	/**
	 *
	 * @return the transaction settings that are based purely on the settings based down through the begin(...) method
	 *         without considering any sail level settings for things like caching or parallel validation.
	 */
	private Settings getLocalTransactionSettings() {
		Settings localTransactionSettings = new Settings();

		Arrays.stream(transactionSettingsRaw)
				.filter(Objects::nonNull)
				.forEach(setting -> {
					if (setting instanceof ValidationApproach) {
						localTransactionSettings.validationApproach = (ValidationApproach) setting;
					}
					if (setting instanceof ShaclSail.TransactionSettings.PerformanceHint) {
						switch (((ShaclSail.TransactionSettings.PerformanceHint) setting)) {
						case ParallelValidation:
							localTransactionSettings.parallelValidation = true;
							break;
						case SerialValidation:
							localTransactionSettings.parallelValidation = false;
							break;
						case CacheDisabled:
							localTransactionSettings.cacheSelectedNodes = false;
							break;
						case CacheEnabled:
							localTransactionSettings.cacheSelectedNodes = true;
							break;
						}
					}
				});
		return localTransactionSettings;
	}

	@Override
	public void addConnectionListener(SailConnectionListener listener) {
		if (!connectionListenerActive && isValidationEnabled()) {
			super.addConnectionListener(this);
			connectionListenerActive = true;
		}
	}

	boolean isValidationEnabled() {
		return transactionSettings.getValidationApproach() != ValidationApproach.Disabled;
	}

	@Override
	public void removeConnectionListener(SailConnectionListener listener) {
		super.removeConnectionListener(listener);
		connectionListenerActive = false;

	}

	private Sail getNewMemorySail() {
		MemoryStore sail = new MemoryStore();
		sail.setDefaultIsolationLevel(IsolationLevels.NONE);
		sail.init();
		return sail;
	}

	@Override
	public void commit() throws SailException {

		if (!preparedHasRun) {
			prepare();
		}

		long before = 0;
		if (sail.isPerformanceLogging()) {
			before = System.currentTimeMillis();
		}
		previousStateConnection.commit();

		super.commit();
		shapesRepoConnection.commit();

		if (sail.isPerformanceLogging()) {
			logger.info("commit() excluding validation and cleanup took {} ms", System.currentTimeMillis() - before);
		}
		cleanup();
	}

	@Override
	public void addStatement(UpdateContext modify, Resource subj, IRI pred, Value obj, Resource... contexts)
			throws SailException {
		if (useDefaultShapesGraph && contexts.length == 1 && RDF4J.SHACL_SHAPE_GRAPH.equals(contexts[0])) {
			shapesRepoConnection.add(subj, pred, obj, contexts);
			shapeRefreshNeeded = true;
		} else {
			super.addStatement(modify, subj, pred, obj, contexts);
		}
	}

	@Override
	public void removeStatement(UpdateContext modify, Resource subj, IRI pred, Value obj, Resource... contexts)
			throws SailException {
		if (useDefaultShapesGraph && contexts.length == 1 && RDF4J.SHACL_SHAPE_GRAPH.equals(contexts[0])) {
			shapesRepoConnection.remove(subj, pred, obj, contexts);
			shapeRefreshNeeded = true;
		} else {
			super.removeStatement(modify, subj, pred, obj, contexts);
		}
	}

	@Override
	public void addStatement(Resource subj, IRI pred, Value obj, Resource... contexts) throws SailException {
		if (useDefaultShapesGraph && contexts.length == 1 && RDF4J.SHACL_SHAPE_GRAPH.equals(contexts[0])) {
			shapesRepoConnection.add(subj, pred, obj, contexts);
			shapeRefreshNeeded = true;
		} else {
			super.addStatement(subj, pred, obj, contexts);
		}
	}

	@Override
	public void removeStatements(Resource subj, IRI pred, Value obj, Resource... contexts) throws SailException {
		if (useDefaultShapesGraph && contexts.length == 1 && RDF4J.SHACL_SHAPE_GRAPH.equals(contexts[0])) {
			shapesRepoConnection.remove(subj, pred, obj, contexts);
			shapeRefreshNeeded = true;
		} else {
			super.removeStatements(subj, pred, obj, contexts);
		}
	}

	@Override
	public void clear(Resource... contexts) throws SailException {
		if (Arrays.asList(contexts).contains(RDF4J.SHACL_SHAPE_GRAPH)) {
			shapesRepoConnection.clear();
			shapeRefreshNeeded = true;
		}
		super.clear(contexts);
	}

	@Override
	public void rollback() throws SailException {

		if (readableShapesCache != null) {
			readableShapesCache.close();
			readableShapesCache = null;
		}

		if (writableShapesCache != null) {
			writableShapesCache.purge();
			writableShapesCache.close();
			writableShapesCache = null;
		}

		try {
			if (previousStateConnection.isActive()) {
				previousStateConnection.rollback();
			}
		} finally {
			try {
				if (shapesRepoConnection.isActive()) {
					shapesRepoConnection.rollback();
				}

			} finally {

				try {
					if (isActive()) {
						super.rollback();
					}

				} finally {
					cleanup();
				}
			}
		}

	}

	private void cleanup() {
		long before = 0;

		try {
			if (sail.isPerformanceLogging()) {
				before = System.currentTimeMillis();
			}

			logger.debug("Cleanup");

			if (addedStatements != null) {
				if (addedStatements != sail.getBaseSail()) {
					addedStatements.shutDown();
				}
				addedStatements = null;
			}

			if (removedStatements != null) {
				removedStatements.shutDown();
				removedStatements = null;
			}

			addedStatementsSet.clear();
			removedStatementsSet.clear();
			stats = null;
			preparedHasRun = false;
			shapeRefreshNeeded = false;
			shapesModifiedInCurrentTransaction = false;

			currentIsolationLevel = null;

		} finally {
			try {
				cleanupShapesReadWriteLock();

			} finally {
				cleanupReadWriteLock();

			}

			if (sail.isPerformanceLogging()) {
				logger.info("cleanup() took {} ms", System.currentTimeMillis() - before);
			}
		}

	}

	private void cleanupShapesReadWriteLock() {
		try {
			try {
				if (writableShapesCache != null) {
					// we need to refresh the shapes cache!
					writableShapesCache.purge();
					writableShapesCache.close();
				}
			} finally {
				if (readableShapesCache != null) {
					readableShapesCache.close();
				}
			}
		} finally {
			writableShapesCache = null;
			readableShapesCache = null;
		}
	}

	private void cleanupReadWriteLock() {
		try {
			try {
				if (writeLock != null) {
					writeLock.release();
				}
			} finally {
				if (readLock != null) {
					readLock.release();
				}
			}
		} finally {
			writeLock = null;
			readLock = null;
		}
	}

	private ValidationReport validate(List<ContextWithShapes> shapes, boolean validateEntireBaseSail) {

		assert isValidationEnabled();

		try {
			try (ConnectionsGroup connectionsGroup = getConnectionsGroup()) {
				return performValidation(shapes, validateEntireBaseSail, connectionsGroup);
			}
		} finally {
			rdfsSubClassOfReasoner = null;

		}
	}

	void prepareValidation() {

		assert isValidationEnabled();

		if (sail.isRdfsSubClassReasoning()) {
			rdfsSubClassOfReasoner = RdfsSubClassOfReasoner.createReasoner(this);
		}

		if (!isBulkValidation()) {
			fillAddedAndRemovedStatementRepositories();
		}

	}

	ConnectionsGroup getConnectionsGroup() {

		return new ConnectionsGroup(new VerySimpleRdfsBackwardsChainingConnection(this, rdfsSubClassOfReasoner),
				previousStateConnection, addedStatements, removedStatements, stats,
				this::getRdfsSubClassOfReasoner, transactionSettings, sail.sparqlValidation);
	}

	private ValidationReport performValidation(List<ContextWithShapes> shapes, boolean validateEntireBaseSail,
			ConnectionsGroup connectionsGroup) {
		long beforeValidation = 0;

		if (sail.isPerformanceLogging()) {
			beforeValidation = System.currentTimeMillis();
		}

		try {
			Stream<Callable<ValidationResultIterator>> callableStream = shapes
					.stream()
					.flatMap(contextWithShapes -> contextWithShapes.getShapes()
							.stream()
							.map(shape -> new ShapePlanNodeTuple(shape,
									shape.generatePlans(connectionsGroup,
											new ValidationSettings(contextWithShapes.getDataGraph(),
													sail.isLogValidationPlans(), validateEntireBaseSail))))

					)
					.filter(ShapePlanNodeTuple::hasPlanNode)
					.map(shapePlanNodeTuple -> new ShapePlanNodeTuple(shapePlanNodeTuple.getShape(),
							new SingleCloseablePlanNode(shapePlanNodeTuple.getPlanNode())))
					.map(shapePlanNodeTuple -> () -> {

						PlanNode planNode = shapePlanNodeTuple.getPlanNode();
						ValidationExecutionLogger validationExecutionLogger = ValidationExecutionLogger
								.getInstance(sail.isGlobalLogValidationExecution());

						planNode.receiveLogger(validationExecutionLogger);

						// Important to start measuring time before we call .iterator() since the initialisation of the
						// iterator will already do a lot of work if there is for instance a Sort in the pipeline
						// because Sort (among others) will consume its parent iterator and sort the results on
						// initialization!
						long before = 0;
						if (sail.isPerformanceLogging()) {
							before = System.currentTimeMillis();
						}

						if (validationExecutionLogger.isEnabled()) {
							logger.info("Start execution of plan:\n{}\n", shapePlanNodeTuple.getShape().toString());
						}

						try (CloseableIteration<? extends ValidationTuple, SailException> iterator = planNode
								.iterator()) {

							ValidationResultIterator validationResults;

							try {
								validationResults = new ValidationResultIterator(iterator,
										sail.getEffectiveValidationResultsLimitPerConstraint());
							} finally {
								if (validationExecutionLogger.isEnabled()) {
									validationExecutionLogger.flush();
								}
							}

							if (sail.isPerformanceLogging()) {
								long after = System.currentTimeMillis();
								logger.info("Execution of plan took {} ms for:\n{}\n", (after - before),
										shapePlanNodeTuple.getShape().toString());
							}

							if (validationExecutionLogger.isEnabled()) {
								logger.info("Finished execution of plan:\n{}\n",
										shapePlanNodeTuple.getShape().toString());

							}

							if (sail.isLogValidationViolations()) {
								if (!validationResults.conforms()) {
									List<ValidationTuple> tuples = validationResults.getTuples();

									logger.info(
											"SHACL not valid. The following experimental debug results were produced:  \n\t\t{}\n\n{}\n",
											tuples.stream()
													.map(ValidationTuple::toString)
													.collect(Collectors.joining("\n\t\t")),
											shapePlanNodeTuple.getShape().toString()

									);
								}
							}

							return validationResults;
						}
					});

			List<ValidationResultIterator> validationResultIterators;

			if (isParallelValidation()) {

				validationResultIterators = callableStream
						.map(this.sail::submitRunnableToExecutorService)
						// Creating a list is needed to actually make things run multi-threaded, without this the
						// laziness of java streams will make this run serially
						.collect(Collectors.toList())
						.stream()
						.map(f -> {
							try {
								return f.get();
							} catch (InterruptedException | ExecutionException e) {
								throw new RuntimeException(e);
							}
						})
						.collect(Collectors.toList());

			} else {
				validationResultIterators = callableStream.map(c -> {
					try {
						return c.call();
					} catch (Exception e) {
						throw new RuntimeException(e);
					}
				}).collect(Collectors.toList());

			}

			return new LazyValidationReport(validationResultIterators, sail.getValidationResultsLimitTotal());

		} finally {
			if (sail.isPerformanceLogging()) {
				logger.info("Actual validation and generating plans took {} ms",
						System.currentTimeMillis() - beforeValidation);
			}
		}
	}

	private boolean isParallelValidation() {
		return transactionSettings.isParallelValidation();
	}

	void fillAddedAndRemovedStatementRepositories() {

		assert !isBulkValidation();
		assert isValidationEnabled();

		long before = 0;
		if (sail.isPerformanceLogging()) {
			before = System.currentTimeMillis();
		}

		Stream.of(addedStatementsSet, removedStatementsSet)
				.parallel()
				.forEach(set -> {
					Set<Statement> otherSet;
					Sail repository;
					if (set == addedStatementsSet) {
						otherSet = removedStatementsSet;

						if (addedStatements != null && addedStatements != sail.getBaseSail()) {
							addedStatements.shutDown();
						}

						addedStatements = getNewMemorySail();
						repository = addedStatements;

						set.forEach(stats::added);

					} else {
						otherSet = addedStatementsSet;

						if (removedStatements != null) {
							removedStatements.shutDown();
							removedStatements = null;
						}

						removedStatements = getNewMemorySail();
						repository = removedStatements;

						set.forEach(stats::removed);
					}

					try (SailConnection connection = repository.getConnection()) {
						connection.begin(IsolationLevels.NONE);
						set.stream()
								.filter(statement -> !otherSet.contains(statement))
								.flatMap(statement -> rdfsSubClassOfReasoner == null ? Stream.of(statement)
										: rdfsSubClassOfReasoner.forwardChain(statement))
								.forEach(statement -> connection.addStatement(statement.getSubject(),
										statement.getPredicate(), statement.getObject(), statement.getContext()));
						connection.commit();
					}

				});

		if (sail.isPerformanceLogging()) {
			logger.info("fillAddedAndRemovedStatementRepositories() took {} ms", System.currentTimeMillis() - before);
		}

	}

	private IsolationLevel getIsolationLevel() {
		return currentIsolationLevel;
	}

	@Override
	synchronized public void close() throws SailException {
		try {
			if (isActive()) {
				rollback();
			}
		} finally {
			try {
				shapesRepoConnection.close();

			} finally {
				try {
					previousStateConnection.close();

				} finally {
					try {
						serializableConnection.close();

					} finally {
						try {
							previousStateSerializableConnection.close();

						} finally {
							try {
								super.close();
							} finally {
								sail.closeConnection(this);
							}
						}
					}
				}
			}
		}
	}

	@Override
	public void prepare() throws SailException {
		flush();
		boolean useSerializableValidation = shouldUseSerializableValidation() && !isBulkValidation();

		if (useSerializableValidation) {
			writeLock = sail.getWriteLock();
		} else {
			readLock = sail.getReadLock();
		}

		try {
			if (!isValidationEnabled()) {
				logger.debug("Validation skipped because validation was disabled");
				if (shapeRefreshNeeded || !connectionListenerActive) {
					// getting the shapes write lock will ensure that the shapes cache is refreshed when cleanup() is
					// called after commit/rollback
					try {
						writableShapesCache = sail.getCachedShapesForWriting();
					} catch (InterruptedException e) {
						Thread.currentThread().interrupt();
						throw new SailException(e);
					}
				}
				return;
			}

			long before = 0;
			if (sail.isPerformanceLogging()) {
				before = System.currentTimeMillis();
			}

			// Serializable validation uses synchronized validation (with locking) to allow a transaction to run in
			// SNAPSHOT isolation but validate as if it was using SERIALIZABLE isolation

//			if (useSerializableValidation) {
//
//			} else {

			// only allow one transaction to modify the shapes at a time

//			}

			assert !shapeRefreshNeeded
					|| !shapesModifiedInCurrentTransaction : "isShapeRefreshNeeded should trigger shapesModifiedInCurrentTransaction once we have loaded the modified shapes, but shapesModifiedInCurrentTransaction should be null until then";

			// since we are within the locked section we can assume that if there are no shapes to validate then we can
			// skip validation
			if (!shapeRefreshNeeded && !sail.hasShapes()) {
				logger.debug("Validation skipped because there are no shapes to validate");
				return;
			}

			if (!shapeRefreshNeeded && !isBulkValidation() && addedStatementsSet.isEmpty()
					&& removedStatementsSet.isEmpty()) {
				logger.debug("Nothing has changed, nothing to validate.");
				return;
			}

			stats.setEmptyIncludingCurrentTransaction(isEmpty());

			List<ContextWithShapes> currentShapes = null;
			List<ContextWithShapes> shapesAfterRefresh = null;

			if (shapeRefreshNeeded || !connectionListenerActive || isBulkValidation()) {
				if (writableShapesCache == null) {
					try {
						writableShapesCache = sail.getCachedShapesForWriting();
					} catch (InterruptedException e) {
						Thread.currentThread().interrupt();
						throw new SailException(e);
					}
				}

				shapesModifiedInCurrentTransaction = shapeRefreshNeeded;
				shapeRefreshNeeded = false;
				shapesAfterRefresh = sail.getShapes(shapesRepoConnection, this, shapesGraphs);
			} else {

				if (readableShapesCache == null) {
					try {
						readableShapesCache = sail.getCachedShapes();
					} catch (InterruptedException e) {
						Thread.currentThread().interrupt();
						throw new SailException(e);
					}
				}
			}

			if (readableShapesCache != null) {
				currentShapes = readableShapesCache.getData();
			}

			assert currentShapes != null || shapesAfterRefresh != null;
			assert !(currentShapes != null && shapesAfterRefresh != null);

//			if (!isBulkValidation() && addedStatementsSet.isEmpty() && removedStatementsSet.isEmpty()) {
//				if (shapesModifiedInCurrentTransaction && shapesBeforeRefresh != null) {
//					// we can optimize which shapes to revalidate since no data has changed.
//
//
//
//					// TODO: We also need to compare the shapes within each ContextWithShapes
//					HashSet<ContextWithShapes> shapesBeforeRefreshSet = new HashSet<>(shapesBeforeRefresh);
//
//					shapesAfterRefresh = shapesAfterRefresh.stream()
//						.filter(shape -> !shapesBeforeRefreshSet.contains(shape))
//						.collect(Collectors.toList());
//
//				}
//			}

//			if (shapesAfterRefresh.isEmpty()) {
//				logger.debug("Validation skipped because there are no shapes to validate");
//				return;
//			}

			prepareValidation();

			ValidationReport invalidTuples = null;
			if (useSerializableValidation) {
				synchronized (sail) {
					if (!sail.usesSingleConnection()) {
						invalidTuples = serializableValidation(
								shapesAfterRefresh != null ? shapesAfterRefresh : currentShapes);
					}
				}
			}

			if (invalidTuples == null) {
//				if (writeLock != null && writeLock.isActive()) {
// also check if write lock was acquired in prepare() because if it was acquire in one of the other places then we shouldn't downgrade now.
				// also - are there actually any cases that would execute this code while using multiple threads?
//					assert readLock == null;
//					readLock = sail.convertToReadLock(writeLock);
//					writeLock = null;
//				}

				invalidTuples = validate(
						shapesAfterRefresh != null ? shapesAfterRefresh : currentShapes,
						shapesModifiedInCurrentTransaction || isBulkValidation());
			}

			boolean valid = invalidTuples.conforms();

			if (sail.isPerformanceLogging()) {
				logger.info("prepare() including validation excluding locking and super.prepare() took {} ms",
						System.currentTimeMillis() - before);
			}

			if (!valid) {
				throw new ShaclSailValidationException(invalidTuples);
			}

		} finally {

			preparedHasRun = true;

			shapesRepoConnection.prepare();
			previousStateConnection.prepare();
			super.prepare();

		}

	}

	private boolean shouldUseSerializableValidation() {
		return sail.isSerializableValidation() && currentIsolationLevel == IsolationLevels.SNAPSHOT;
	}

	private boolean isBulkValidation() {
		return transactionSettings.getValidationApproach() == ValidationApproach.Bulk;
	}

	private ValidationReport serializableValidation(List<ContextWithShapes> shapesAfterRefresh) {
		try {
			try {
				try (ConnectionsGroup connectionsGroup = new ConnectionsGroup(
						new VerySimpleRdfsBackwardsChainingConnection(serializableConnection, rdfsSubClassOfReasoner),
						previousStateSerializableConnection, addedStatements, removedStatements, stats,
						this::getRdfsSubClassOfReasoner, transactionSettings, sail.sparqlValidation)) {

					connectionsGroup.getBaseConnection().begin(IsolationLevels.SNAPSHOT);
					// actually force a transaction to start
					connectionsGroup.getBaseConnection().hasStatement(null, null, null, false);

					connectionsGroup.getPreviousStateConnection().begin(IsolationLevels.SNAPSHOT);
					// actually force a transaction to start
					connectionsGroup.getPreviousStateConnection().hasStatement(null, null, null, false);

					stats.setEmptyBeforeTransaction(ConnectionHelper.isEmpty(connectionsGroup.getBaseConnection()));

					try (SailConnection connection = addedStatements.getConnection()) {
						SailConnection baseConnection = connectionsGroup.getBaseConnection();
						ConnectionHelper.transferStatements(connection, baseConnection::addStatement);
					}

					try (SailConnection connection = removedStatements.getConnection()) {
						SailConnection baseConnection = connectionsGroup.getBaseConnection();
						ConnectionHelper.transferStatements(connection, baseConnection::removeStatements);
					}

					serializableConnection.flush();

					return performValidation(shapesAfterRefresh,
							shapesModifiedInCurrentTransaction || isBulkValidation(), connectionsGroup);

				} finally {
					serializableConnection.rollback();
				}
			} finally {
				previousStateSerializableConnection.rollback();
			}
		} finally {
			rdfsSubClassOfReasoner = null;

		}
	}

	@Override
	public void statementAdded(Statement statement) {
		if (preparedHasRun) {
			throw new IllegalStateException("Detected changes after prepare() has been called.");
		}
		checkIfShapesRefreshIsNeeded(statement);
		boolean add = addedStatementsSet.add(statement);
		if (!add) {
			removedStatementsSet.remove(statement);
		}

		checkTransactionalValidationLimit();

	}

	@Override
	public void statementRemoved(Statement statement) {
		if (preparedHasRun) {
			throw new IllegalStateException("Detected changes after prepare() has been called.");
		}
		checkIfShapesRefreshIsNeeded(statement);

		boolean add = removedStatementsSet.add(statement);
		if (!add) {
			addedStatementsSet.remove(statement);
		}

		checkTransactionalValidationLimit();
	}

	private void checkIfShapesRefreshIsNeeded(Statement statement) {

		if (!shapeRefreshNeeded) {
			for (IRI shapesGraph : shapesGraphs) {
				if (Objects.equals(statement.getContext(), shapesGraph)) {
					shapeRefreshNeeded = true;
					break;
				}
			}
		}
	}

	private void checkTransactionalValidationLimit() {
		if ((addedStatementsSet.size() + removedStatementsSet.size()) > sail.getTransactionalValidationLimit()) {
			if (shouldUseSerializableValidation()) {
				logger.debug(
						"Transaction size limit exceeded, could not switch to bulk validation because serializable validation is enabled.");
			} else {
				logger.debug("Transaction size limit exceeded, reverting to bulk validation.");
				removeConnectionListener(this);
				Settings bulkValidation = getLocalTransactionSettings();
				bulkValidation.validationApproach = ShaclSail.TransactionSettings.ValidationApproach.Bulk;
				getTransactionSettings().applyTransactionSettings(bulkValidation);
				removedStatementsSet.clear();
				addedStatementsSet.clear();
			}
		}
	}

	public RdfsSubClassOfReasoner getRdfsSubClassOfReasoner() {
		return rdfsSubClassOfReasoner;
	}

	@Override
	public CloseableIteration<? extends Statement, SailException> getStatements(Resource subj, IRI pred, Value obj,
			boolean includeInferred, Resource... contexts) throws SailException {
		if (useDefaultShapesGraph && contexts.length == 1 && RDF4J.SHACL_SHAPE_GRAPH.equals(contexts[0])) {
			return ConnectionHelper
					.getCloseableIteration(shapesRepoConnection.getStatements(subj, pred, obj, includeInferred));
		}

		return super.getStatements(subj, pred, obj, includeInferred, contexts);

	}

	@Override
	public boolean hasStatement(Resource subj, IRI pred, Value obj, boolean includeInferred, Resource... contexts)
			throws SailException {

		if (useDefaultShapesGraph && contexts.length == 1 && RDF4J.SHACL_SHAPE_GRAPH.equals(contexts[0])) {
			return shapesRepoConnection.hasStatement(subj, pred, obj, includeInferred);
		}

		return super.hasStatement(subj, pred, obj, includeInferred, contexts);

	}

	private boolean isEmpty() {
		return ConnectionHelper.isEmpty(this);
	}

	public ValidationReport revalidate() {

		if (!isActive()) {
			throw new IllegalStateException("No active transaction!");
		}
		return validate(sail.getShapes(shapesRepoConnection, this, shapesGraphs), true);
	}

	Settings getTransactionSettings() {
		return transactionSettings;
	}

	public static class Settings {

		private ValidationApproach validationApproach;
		private Boolean cacheSelectedNodes;
		private Boolean parallelValidation;
		private IsolationLevel isolationLevel;

		public Settings() {
		}

		public Settings(boolean cacheSelectNodes, boolean validationEnabled, boolean parallelValidation,
				IsolationLevel isolationLevel) {
			this.cacheSelectedNodes = cacheSelectNodes;
			if (!validationEnabled) {
				validationApproach = ValidationApproach.Disabled;
			} else {
				this.validationApproach = ValidationApproach.Auto;
			}
			this.parallelValidation = parallelValidation;
			this.isolationLevel = isolationLevel;
		}

		public ValidationApproach getValidationApproach() {
			return validationApproach;
		}

		public boolean isCacheSelectNodes() {
			return cacheSelectedNodes;
		}

		public boolean isParallelValidation() {
			return parallelValidation;
		}

		public IsolationLevel getIsolationLevel() {
			return isolationLevel;
		}

		static ValidationApproach getMostSignificantValidationApproach(
				ValidationApproach base,
				ValidationApproach overriding) {
			if (base == null && overriding == null) {
				return ValidationApproach.Auto;
			}

			return ValidationApproach.getHighestPriority(base, overriding);

		}

		void applyTransactionSettings(Settings transactionSettingsLocal) {
			// get the most significant validation approach first (eg. if validation is disabled on the sail level, then
			// validation can not be enabled on the transaction level
			validationApproach = getMostSignificantValidationApproach(validationApproach,
					transactionSettingsLocal.validationApproach);

			// apply restrictions first
			if (validationApproach == ValidationApproach.Bulk) {
				cacheSelectedNodes = false;
				parallelValidation = false;
			}

			// override settings
			if (transactionSettingsLocal.parallelValidation != null) {
				parallelValidation = transactionSettingsLocal.parallelValidation;
			}

			if (transactionSettingsLocal.cacheSelectedNodes != null) {
				cacheSelectedNodes = transactionSettingsLocal.cacheSelectedNodes;
			}

			assert transactionSettingsLocal.isolationLevel == null;

			if (isolationLevel == IsolationLevels.SERIALIZABLE) {
				if (parallelValidation) {
					logger.warn("Parallel validation is not compatible with SERIALIZABLE isolation level!");
				}

				parallelValidation = false;
			}

		}

		@Override
		public String toString() {
			return "Settings{" +
					"validationApproach=" + validationApproach +
					", cacheSelectedNodes=" + cacheSelectedNodes +
					", parallelValidation=" + parallelValidation +
					", isolationLevel=" + isolationLevel +
					'}';
		}

		public void switchToBulkValidation() {
			ValidationApproach newValidationApproach = getMostSignificantValidationApproach(validationApproach,
					ValidationApproach.Bulk);

			if (newValidationApproach != this.validationApproach) {
				this.validationApproach = newValidationApproach;
				parallelValidation = false;
				cacheSelectedNodes = false;
			}
		}
	}

	static class ShapePlanNodeTuple {
		private final Shape shape;
		private final PlanNode planNode;

		public ShapePlanNodeTuple(Shape shape, PlanNode planNode) {
			this.shape = shape;
			this.planNode = planNode;
		}

		public Shape getShape() {
			return shape;
		}

		public PlanNode getPlanNode() {
			return planNode;
		}

		public boolean hasPlanNode() {
			return !(planNode instanceof EmptyNode);
		}
	}

}
