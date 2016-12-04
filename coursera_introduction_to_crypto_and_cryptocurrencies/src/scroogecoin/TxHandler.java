package scroogecoin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.PriorityQueue;

public class TxHandler {

	public static final int VALID = 1;
	public static final int INVALID = -1;
	public static final int POT_VALID = 0;

	private UTXOPool up;

	/**
	 * Creates a public ledger whose current UTXOPool (collection of unspent
	 * transaction outputs) is utxoPool. This should make a defensive copy of
	 * utxoPool by using the UTXOPool(UTXOPool uPool) constructor.
	 */
	public TxHandler(UTXOPool utxoPool) {
		up = new UTXOPool(utxoPool);
	}

	/** Returns true if
	   * (1) all outputs claimed by tx are in the current UTXO pool
	   * (2) the signatures on each input of tx are valid
	   * (3) no UTXO is claimed multiple times by tx
	   * (4) all of tx’s output values are non-negative
	   * (5) the sum of tx’s input values is greater than or equal 
	   * to the sum of its output values; and false otherwise.
	   */
	public boolean isValidTx(Transaction tx) {

		ArrayList<UTXO> txUTXOList = new ArrayList<UTXO>();

		double inputSum = 0;
		double outputSum = 0;

		int index = 0;

		for (Transaction.Input in : tx.getInputs()) {

			UTXO inUTXO = new UTXO(in.prevTxHash, in.outputIndex);

			// if the transaction pool doesn't contain it already
			if (!up.contains(inUTXO))
				return false; // 1

			inputSum += up.getTxOutput(inUTXO).value;

			// Check Signature
			if(!Crypto.verifySignature(up.getTxOutput(inUTXO).address, 
					tx.getRawDataToSign(index), 
					in.signature))
				return false; // 2

			// no UTXO is claimed multiple times by tx
			if (txUTXOList.contains(inUTXO))
				return false; // 3

			txUTXOList.add(inUTXO);

			index++;
		}

		for (Transaction.Output out : tx.getOutputs()) {
			if (out.value < 0)
				return false; // 4
			outputSum += out.value;
		}

		if (outputSum > inputSum)
			return false; // 5

		return true;
	}

	/*
	 * classifies transaction AND creates a wrapper.
	 */
	public TxWrapper wrapTx(Transaction tx) {
		int result = VALID;
		ArrayList<UTXO> seenUTXO = new ArrayList<UTXO>();

		double inSum = 0;
		double outSum = 0;

		int index = 0;

		for (Transaction.Input in : tx.getInputs()) {

			UTXO checkUTXO = new UTXO(in.prevTxHash, in.outputIndex);
			if (seenUTXO.contains(checkUTXO))
				return null; // 3
			// no UTXO is claimed multiple times by tx

			seenUTXO.add(checkUTXO);
			// if the transaction pool doesn't contain it already
			if (!up.contains(checkUTXO)) {
				result = POT_VALID;
				inSum = -1;
			} else {
				inSum += up.getTxOutput(checkUTXO).value;
				if(!Crypto.verifySignature(up.getTxOutput(checkUTXO).address, 
						tx.getRawDataToSign(index), 
						in.signature))
					return null; // 2
			}
			// Check Signature

			index++;
		}

		for (Transaction.Output out : tx.getOutputs()) {
			if (out.value < 0)
				return null; // 4
			outSum += out.value;
		}

		if (inSum != -1 && outSum > inSum)
			return null; // 5

		return new TxWrapper(new Transaction(tx), inSum - outSum, result);
	}

	// this only checks if all the inputs are in the UTXO pool
	public int quickCheck(TxWrapper wrapped) {
		Transaction tx = wrapped.getTx();
		double inSum = 0;
		int index = 0;
		for (Transaction.Input in : tx.getInputs()) {

			UTXO checkUTXO = new UTXO(in.prevTxHash, in.outputIndex);

			// if the transaction pool doesn't contain it already
			if (!up.contains(checkUTXO)) {
				return POT_VALID;
			}

			if(!Crypto.verifySignature(up.getTxOutput(checkUTXO).address, 
					tx.getRawDataToSign(index), 
					in.signature))
				return INVALID; // 2
			inSum += up.getTxOutput(checkUTXO).value;
			index++;
		}
		wrapped.setFee(wrapped.getFee() - inSum);
		return VALID;
	}

	/**
	 * Handles each epoch by receiving an unordered array of proposed
	 * transactions, checking each transaction for correctness, returning a
	 * mutually valid array of accepted transactions, and updating the current
	 * UTXO pool as appropriate.
	 */
	public Transaction[] handleTxs(Transaction[] possibleTxs) {
		 
		/*
		 * (1) first create a hash to transaction table for possibleTxs
		 * 
		 * (2) for each transaction, if it's invalid, then kill it. If all
		 * inputs are in UTXOPool, add it to nbrsOfGood. For each input, add
		 * that transaction to the "refs" list of the referenced address. (3)
		 * order potGoodTxs by transaction fee (make txFee a method). Repeat
		 * until potGoodTxs is empty: take the transaction tx with maximum fee
		 * in nbrsOfGood and if it's valid, then put it in UTXOPool. Take any
		 * transactions that attempt to double-spend the addresses just spent
		 * and delete them from potGoodTxs (optional). Check neighbours of tx; if
		 * they are valid put them into nbrsOfGood.
		 */
		HashMap<byte[], TxWrapper> hashToTx = new HashMap<byte[], TxWrapper>();
		PriorityQueue<TxWrapper> nbrsOfGood = new PriorityQueue<TxWrapper>();
		ArrayList<TxWrapper> potGoodTxs = new ArrayList<TxWrapper>();
		ArrayList<Transaction> goodTxs = new ArrayList<Transaction>();

		for (Transaction tx : possibleTxs) {
			TxWrapper wrapped = wrapTx(tx);
			if (wrapped == null)
				continue;// we don't put this in the set.
			hashToTx.put(tx.getHash(), wrapped);

			switch (wrapped.getValidity()) {
			case VALID:
				nbrsOfGood.add(wrapped);
				break;
			case POT_VALID:
				potGoodTxs.add(wrapped);
				break;
			// case INVALID:
			// do nothing
			}
		}

		for (TxWrapper wrapped : potGoodTxs) {
			for (Transaction.Input in : wrapped.getTx().getInputs()) {
				byte[] hash = in.prevTxHash;
				TxWrapper origin = hashToTx.get(hash);
				UTXO checkUTXO = new UTXO(in.prevTxHash, in.outputIndex);

				if (origin == null && (!up.contains(checkUTXO))) {
					break;
					// can do another check to see if we can actually remove
					// this
					// but it's not a big deal.
				}
				origin.addRef(wrapped);
			}
		}

		while (!nbrsOfGood.isEmpty()) {
			TxWrapper top = nbrsOfGood.poll();

			if (quickCheck(top) != VALID)
				continue;

			goodTxs.add(top.getTx());
			// Remove old UTXOs from Pool
			for (Transaction.Input in : top.getTx().getInputs()) {
				UTXO delUTXO = new UTXO(in.prevTxHash, in.outputIndex);
				up.removeUTXO(delUTXO);
			}
			// reuse code
			for (int j = 0; j < top.getTx().getOutputs().size(); j++) {
				UTXO newUTXO = new UTXO(top.getTx().getHash(), j);
				up.addUTXO(newUTXO, top.getTx().getOutputs().get(j));
			}

			// destroy all things that were invalidated.

			for (TxWrapper nbr : top.getRefs()) {
				if (quickCheck(nbr) == VALID) {
					nbrsOfGood.add(nbr);
				}
				// if nbr is valid
				// then add it to nbrsOfGood
			}
		}

		Transaction[] tArr = new Transaction[goodTxs.size()];
		tArr = goodTxs.toArray(tArr);
		return tArr;
	}

	// node for graph
	public class TxWrapper implements Comparable<TxWrapper> {
		
		private Transaction tx;
		private ArrayList<TxWrapper> refs;
		private double fee;
		private int validity;

		public TxWrapper(Transaction tx, double fee, int validity) {
			this.setTx(tx);
			this.setFee(fee);
			this.setValidity(validity);
			this.refs = new ArrayList<TxWrapper>();
		}

		public Transaction getTx() {
			return tx;
		}

		public void setTx(Transaction tx) {
			this.tx = tx;
		}

		public ArrayList<TxWrapper> getRefs() {
			return refs;
		}

		public int compareTo(TxWrapper tx2) {
			return Double.compare(fee, tx2.getFee());
		}

		public double getFee() {
			return fee;
		}

		public void setFee(double fee) {
			this.fee = fee;
		}

		public int getValidity() {
			return validity;
		}

		public void setValidity(int validity) {
			this.validity = validity;
		}

		public void addRef(TxWrapper tx2) {
			refs.add(tx2);
		}
	}

}