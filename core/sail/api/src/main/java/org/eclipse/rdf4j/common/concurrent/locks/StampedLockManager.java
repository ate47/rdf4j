/*******************************************************************************
 * Copyright (c) 2022 Eclipse RDF4J contributors.
 *  All rights reserved. This program and the accompanying materials
 *  are made available under the terms of the Eclipse Distribution License v1.0
 *  which accompanies this distribution, and is available at
 *  http://www.eclipse.org/org/documents/edl-v10.php.
 ******************************************************************************/

package org.eclipse.rdf4j.common.concurrent.locks;

import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.StampedLock;

import org.eclipse.rdf4j.common.concurrent.locks.diagnostics.LockCleaner;
import org.eclipse.rdf4j.common.concurrent.locks.diagnostics.LockDiagnostics;
import org.eclipse.rdf4j.common.concurrent.locks.diagnostics.LockMonitoring;
import org.eclipse.rdf4j.common.concurrent.locks.diagnostics.LockTracking;
import org.slf4j.LoggerFactory;

/**
 * An abstract base implementation of a read/write-lock manager.
 *
 * @author Håvard M. Ottestad
 */
public class StampedLockManager implements ReadWriteLockManager {

	private final LockMonitoring readLockMonitoring;
	private final LockMonitoring writeLockMonitoring;

	// StampedLock for handling writers.
	final StampedLock stampedLock = new StampedLock();

	// milliseconds to wait when calling the try-lock method of the stamped lock
	private final int tryWriteLockMillis;

	public StampedLockManager() {
		this(false);
	}

	public StampedLockManager(boolean trackLocks) {
		this(trackLocks, LockMonitoring.INITIAL_WAIT_TO_COLLECT);
	}

	public StampedLockManager(boolean trackLocks, int waitToCollect) {
		this("", waitToCollect, LockDiagnostics.fromLegacyTracking(trackLocks));
	}

	public StampedLockManager(String alias, LockDiagnostics... lockDiagnostics) {
		this(alias, LockMonitoring.INITIAL_WAIT_TO_COLLECT, lockDiagnostics);
	}

	public StampedLockManager(String alias, int waitToCollect, LockDiagnostics... lockDiagnostics) {

		this.tryWriteLockMillis = Math.min(1000, waitToCollect);

		boolean releaseAbandoned = false;
		boolean detectStalledOrDeadlock = false;
		boolean stackTrace = false;

		for (LockDiagnostics lockDiagnostic : lockDiagnostics) {
			switch (lockDiagnostic) {
			case releaseAbandoned:
				releaseAbandoned = true;
				break;
			case detectStalledOrDeadlock:
				detectStalledOrDeadlock = true;
				break;
			case stackTrace:
				stackTrace = true;
				break;
			}
		}

		if (lockDiagnostics.length == 0) {

			readLockMonitoring = LockMonitoring
					.wrap(Lock.ExtendedSupplier.wrap(this::createReadLockInner, this::tryReadLockInner));
			writeLockMonitoring = LockMonitoring
					.wrap(Lock.ExtendedSupplier.wrap(this::createWriteLockInner, this::tryWriteLockInner));

		} else if (releaseAbandoned && !detectStalledOrDeadlock) {

			readLockMonitoring = new LockCleaner(
					stackTrace,
					alias + "_READ",
					LoggerFactory.getLogger(this.getClass()),
					Lock.ExtendedSupplier.wrap(this::createReadLockInner, this::tryReadLockInner)
			);

			writeLockMonitoring = new LockCleaner(
					stackTrace,
					alias + "_WRITE",
					LoggerFactory.getLogger(this.getClass()),
					Lock.ExtendedSupplier.wrap(this::createWriteLockInner, this::tryWriteLockInner)
			);

		} else {

			readLockMonitoring = new LockTracking(
					stackTrace,
					alias + "_READ",
					LoggerFactory.getLogger(this.getClass()),
					waitToCollect,
					Lock.ExtendedSupplier.wrap(this::createReadLockInner, this::tryReadLockInner)
			);

			writeLockMonitoring = new LockTracking(
					stackTrace,
					alias + "_WRITE",
					LoggerFactory.getLogger(this.getClass()),
					waitToCollect,
					Lock.ExtendedSupplier.wrap(this::createWriteLockInner, this::tryWriteLockInner)
			);
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean isWriterActive() {
		return stampedLock.isWriteLocked();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean isReaderActive() {
		return stampedLock.isReadLocked();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void waitForActiveWriter() throws InterruptedException {
		while (isWriterActive()) {
			spinWait();
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void waitForActiveReaders() throws InterruptedException {
		while (isReaderActive()) {
			spinWait();
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Lock getReadLock() throws InterruptedException {
		return readLockMonitoring.getLock();
	}

	private Lock createReadLockInner() throws InterruptedException {
		return new ReadLock(stampedLock, stampedLock.readLockInterruptibly());
	}

	/**
	 * TODO
	 */
	public OptimisticReadLock getOptimisticReadLock() throws InterruptedException {
		long optimisticReadStamp = stampedLock.tryOptimisticRead();
		if (optimisticReadStamp != 0) {
			return new OptimisticReadLock(stampedLock, optimisticReadStamp);
		} else {
			long readLock = stampedLock.readLockInterruptibly();
			try {
				optimisticReadStamp = stampedLock.tryOptimisticRead();
				if (optimisticReadStamp == 0) {
					throw new IllegalMonitorStateException("Optimistic read should be guaranteed while write locked!");
				}
				return new OptimisticReadLock(stampedLock, optimisticReadStamp);
			} finally {
				stampedLock.unlockRead(readLock);
			}

		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Lock getWriteLock() throws InterruptedException {
		return writeLockMonitoring.getLock();
	}

	private Lock createWriteLockInner() throws InterruptedException {

		// Acquire a write-lock.
		long writeStamp = writeLockInterruptibly();
		return new WriteLock(stampedLock, writeStamp);
	}

	private long writeLockInterruptibly() throws InterruptedException {

		if (writeLockMonitoring.requiresManualCleanup()) {
			long writeStamp;
			do {
				if (Thread.interrupted()) {
					throw new InterruptedException();
				}

				writeStamp = stampedLock.tryWriteLock(tryWriteLockMillis, TimeUnit.MILLISECONDS);

				if (writeStamp == 0) {

					writeLockMonitoring.runCleanup();
					readLockMonitoring.runCleanup();
				}
			} while (writeStamp == 0);
			return writeStamp;
		} else {
			return stampedLock.writeLockInterruptibly();
		}

	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Lock tryReadLock() {
		return readLockMonitoring.tryLock();
	}

	private Lock tryReadLockInner() {
		long stamp = stampedLock.tryReadLock();
		if (stamp != 0) {
			return new ReadLock(stampedLock, stamp);
		} else {
			return null;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Lock tryWriteLock() {
		return writeLockMonitoring.tryLock();
	}

	private Lock tryWriteLockInner() {
		// Try to acquire a write-lock.
		long stamp = stampedLock.tryWriteLock();
		if (stamp != 0) {
			return new WriteLock(stampedLock, stamp);
		} else {
			return null;
		}

	}

	private void spinWait() throws InterruptedException {
		Thread.onSpinWait();

		writeLockMonitoring.runCleanup();
		readLockMonitoring.runCleanup();

		if (Thread.interrupted()) {
			throw new InterruptedException();
		}

	}

	private static class WriteLock implements Lock {

		private final StampedLock lock;
		private long stamp;

		public WriteLock(StampedLock lock, long stamp) {
			assert stamp != 0;
			this.lock = lock;
			this.stamp = stamp;
		}

		@Override
		public boolean isActive() {
			return stamp != 0;
		}

		@Override
		public void release() {
			long temp = stamp;
			stamp = 0;

			if (temp == 0) {
				throw new IllegalMonitorStateException("Trying to release a lock that is not locked");
			}

			lock.unlockWrite(temp);
		}
	}

	private static class ReadLock implements Lock {

		private final StampedLock stampedLock;
		private final long stamp;
		private boolean locked = true;

		public ReadLock(StampedLock stampedLock, long stamp) {
			this.stampedLock = stampedLock;
			this.stamp = stamp;
		}

		@Override
		public boolean isActive() {
			return locked;
		}

		@Override
		public void release() {
			if (!locked) {
				throw new IllegalMonitorStateException("Trying to release a lock that is not locked");
			}

			locked = false;
			stampedLock.unlockRead(stamp);
		}
	}

	public static class OptimisticReadLock implements Lock {

		private final StampedLock stampedLock;
		private final long optimisticReadStamp;

		public OptimisticReadLock(StampedLock stampedLock, long stamp) {
			this.stampedLock = stampedLock;
			this.optimisticReadStamp = stamp;
		}

		@Override
		public boolean isActive() {
			return stampedLock.validate(optimisticReadStamp);
		}

		@Override
		public void release() {
			// no-op
		}
	}

}
