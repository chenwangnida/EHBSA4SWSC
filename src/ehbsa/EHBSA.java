package ehbsa;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.DoubleStream;

import org.apache.commons.lang3.ArrayUtils;
import org.apache.commons.math3.distribution.EnumeratedIntegerDistribution;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.jgrapht.traverse.GraphIterator;

import com.google.common.collect.Sets;

import wsc.data.pool.Service;
import wsc.graph.ServiceEdge;
import wsc.graph.ServiceGraph;
import wsc.graph.ServiceInput;
import wsc.graph.ServiceOutput;
import wsc.owl.bean.OWLClass;
import wsc.problem.WSCIndividual;
import wsc.problem.WSCInitializer;

public class EHBSA {
	private int m_i; // size of i dimension
	private int m_j; // size of j dimension
	double[][] m_node; // a edge histogram matrix (EHM)
	private double m_bRatio = 0.0002;// a bias for EHM

	private int sizeOfSDG;

	private List<WSCIndividual> m_pop = new ArrayList<WSCIndividual>();

	public EHBSA(int m_i, int m_j) {
		this.m_i = m_i;
		this.m_j = m_j;
		m_node = new double[m_i][m_j]; // initial an edge histogram matrix (NHM)
	}

	/**
	 * initial correct entries for EHM as we only consider the dependencies in a
	 * full service dependency graph.
	 *
	 * @param NULL
	 */
	public double[][] initialEHM() {

		// set -1 to all entries in EHM
		for (int i = 0; i < m_i; i++) {
			for (int j = 0; j < m_j; j++) {
				m_node[i][j] = -1;
			}
		}

		for (int j = 1; j < m_j; j++) {
			// initialize the list to put all labelled predecessors for all required inputs
			// of service index j
			List<Set<Service>> scanList4Predecessors = new ArrayList<Set<Service>>();

			// query ontology tree from 0 to end to get direct predecessors
			Service targetSer = WSCInitializer.Index2ServiceMap.get(j);
			for (ServiceInput input : targetSer.getInputList()) {
				OWLClass inputConceptClass = WSCInitializer.initialWSCPool.getSemanticsPool().owlClassHashMap
						.get(WSCInitializer.initialWSCPool.getSemanticsPool().owlInstHashMap.get(input.getInput())
								.getRdfType().getResource().substring(1));
				scanList4Predecessors
						.add(WSCInitializer.TaxonomyNodeMap.get(inputConceptClass.getID()).servicesWithOutput);
			}

			// intersection of sets in scanList4Predecessors
			Set<Service> intersection = scanList4Predecessors.get(0);
			for (Set<Service> scan : scanList4Predecessors.subList(1, scanList4Predecessors.size())) {
				intersection = Sets.union(intersection, scan);
			}

			// set 0 to valid entries in EHM
			for (Service ser : intersection) {
				// I do not consider these service produce its own inputs
				if (ser.getServiceIndex() != j) {
					m_node[ser.getServiceIndex()][j] = 0;
					sizeOfSDG++;
				}
			}
		}
		// System.out.println("size of entries before applying layer information" +
		// sizeOfSDG);

		return m_node;
	}

	/**
	 * Learn EHM from current population.
	 *
	 */
	public double[][] learnEHMfromPop() {
		// To Do: set bias
		setBias4EHM();

		// add bias to only correct entries of NHM
		for (int i = 0; i < m_i; i++) {
			for (int j = 0; j < m_j; j++) {

				if (m_node[i][j] != -1) {
					m_node[i][j] += m_bRatio;
				}
			}
		}

		// iterate individual
		for (WSCIndividual indi : m_pop) {
			Set<ServiceEdge> indiEdges = indi.getDagRepresentation().edgeSet();
			for (ServiceEdge edge : indiEdges) {
				int i = WSCInitializer.serviceIndexBiMap.inverse().get(edge.getSourceService());
				int j = WSCInitializer.serviceIndexBiMap.inverse().get(edge.getTargetService());
				m_node[i][j] += 1;
			}
		}
		return m_node;
	}

	public final void setBias4EHM() {

		int sum_pop_edge = 0;
		for (WSCIndividual indi : m_pop) {
			sum_pop_edge += indi.getEdgeSize();
		}

		m_bRatio = (sum_pop_edge * m_bRatio) / sizeOfSDG; // bias
	}

	/**
	 * Our proposed guided EHBSA-based backward graph-building algorithm.
	 *
	 * @param sampleSize
	 *            it is equals to the half of the population size
	 * @param random
	 */
	public List<WSCIndividual> sampling4EHBSA(int sampleSize, Random random) {

		List<WSCIndividual> sampled_pop = new ArrayList<WSCIndividual>();

		// EHBSA/WO Sampling sampleSize numbers of individuals
		for (int no_sample = 0; no_sample < sampleSize; no_sample++) {

			// reset satisfactions of all service inputs to false

			for (Service s : WSCInitializer.Index2ServiceMap.values()) {
				if (s.getInputList() != null) {
					for (ServiceInput serinput : s.getInputList()) {
						serinput.setSatified(false);
					}
				}
			}

			// reset satisfactions of all service outputs to false

			for (Service s : WSCInitializer.Index2ServiceMap.values()) {
				if (s.getOutputList() != null) {
					for (ServiceOutput seroutput : s.getOutputList()) {
						seroutput.setSatified(false);
					}
				}
			}

			// initial graph and its corresponding individual
			ServiceGraph graph = new ServiceGraph(ServiceEdge.class);
			graph.addVertex("endNode");

			WSCIndividual sampledIndi = new WSCIndividual();
			sampledIndi.setDagRepresentation(graph);

			// initial serSet with endNode
			Queue<Service> serQue = new LinkedList<Service>();

			// initial serSet with endSer
			serQue.add(WSCInitializer.endSer);

			while (!serQue.isEmpty()) { // one stop condition for returning sampled individual

				Service s = serQue.remove();

				// one condition for moving to next service
				if (s.getServiceID() == "startNode") {
					continue;
				}

				// another condition for moving to next service
				boolean Move2next = true;
				if (s.getInputList() != null) {
					for (ServiceInput input : s.getInputList()) {
						Move2next &= input.isSatified();
					}
				}

				if (Move2next == true) {
					continue;
				}

				// set one dimension for sampling
				int j = s.getServiceIndex();

				// flag for startNode
				// boolean startNodeSatisfied = false;

				// startNode is always checked in advance
				if ((m_node[0][j] != -1)) {
					// write a loop to check their dependency

					int NoOfMatchedUnsatisfiedIn = WSCInitializer.initialWSCPool.createEdge4TwoSer(graph,
							WSCInitializer.startSer, s);

					if (NoOfMatchedUnsatisfiedIn > 0) {
						// put the sampled predecessor into serSet
						if (!serQue.contains(WSCInitializer.startSer)) {
							serQue.add(WSCInitializer.startSer);
						}

						// check number of unsatisfied inputs of service s
						int noOfUnsatisfiedIn = 0;
						for (ServiceInput in : s.getInputList()) {
							if (!in.isSatified()) {
								noOfUnsatisfiedIn++;
							}
						}

						if (noOfUnsatisfiedIn == 0) {// shall we move to next dimension for sampling
							continue;// no need to execute sampling for s
						}
						// if start can fulfill any input of s
						// startNodeSatisfied = true;
					}
				}

				// identify the layer-related indexes;
				nextDimensionLoop: for (int layerNo = s.getLayer(); layerNo >= 0; layerNo--) {
					nextLayerLoop: for (int entry : WSCInitializer.layers4SerIndex.get(layerNo)) {
						if (m_node[entry][j] != -1) { // sample from this layer

							// set the position counter
							int p_counter = 0;

							// initial a candidate node copy from layer
							List<Integer> layer = WSCInitializer.layers4SerIndex.get(layerNo);
							int[] c_candidates = new int[layer.size()];
							for (int m = 0; m < layer.size(); m++) {
								c_candidates[m] = layer.get(m);
							}

							samplingLoop: while (true) {

								// break nextDimensionLoop condition for sampling next dimension
								int noOfUnsatisfiedIn = 0;
								for (ServiceInput in : s.getInputList()) {
									if (!in.isSatified()) {
										noOfUnsatisfiedIn++;
									}
								}

								if (noOfUnsatisfiedIn == 0) {// shall we move to next dimension for sampling
									break nextDimensionLoop;
								}

								// break inner loop to sample from next dimension
								if (layer.size() == p_counter) {
									break nextLayerLoop; // break and sample from net layer
								}

								// sample one predecessor of current j
								double[] discreteProbabilities = new double[layer.size() - p_counter];

								// calculate probability and put them into probability[]
								double sum_proba = 0;
								for (int c : c_candidates) {
									if (m_node[c][j] != -1) {
										sum_proba += m_node[c][j];
									}
								}

								int m = 0;

								for (int c : c_candidates) {

									// for -1 , we set 0 probability to its distribution
									if (m_node[c][j] == -1) {
										discreteProbabilities[m] = 0;
										// System.out.println(c + " proba: " + discreteProbabilities[m]);

									} else {
										discreteProbabilities[m] = m_node[c][j] / sum_proba;
										// System.out.println(c + " proba: " + discreteProbabilities[m]);

									}
									m++;
								}

								double sum = DoubleStream.of(discreteProbabilities).sum();
								if (sum == 0) {
									break nextLayerLoop;
								}

								// if start must be sampled first if it is in c_candidates and removed from
								// array c_candidates
								int sampledIndexOfPredecessor = sampling(c_candidates, discreteProbabilities,
										random)[0];

								// sample one predecessor from j

								String PredecessorStr = WSCInitializer.serviceIndexBiMap.get(sampledIndexOfPredecessor);

								if (PredecessorStr == s.getServiceID()) {
									System.out.println("error break");
								}

								// remove x from numsToGenerate
								c_candidates = ArrayUtils.removeElement(c_candidates, sampledIndexOfPredecessor);

								// if (!allSuccessors.contains(PredecessorStr)) {
								Service predecessor = WSCInitializer.Index2ServiceMap.get(sampledIndexOfPredecessor);

								// add predecessor and all services in queue to check their satisfaction for the
								// exampled node
								Set<Service> unsatisfiedSer = new HashSet<Service>();

								Iterator<Service> queIter = serQue.iterator();
								while (queIter.hasNext()) {
									Service ser = queIter.next();
									if (!ser.getServiceID().equals("startNode")) {
										unsatisfiedSer.add(ser);
									}
								}

								unsatisfiedSer.add(s);

								// write a loop to check their dependency
								for (Service checkedSer : unsatisfiedSer) {
									if (checkedSer.getServiceID() != predecessor.getServiceID()) {

										int NoOfMatchedUnsatisfiedIn = WSCInitializer.initialWSCPool
												.createEdge4TwoSer(graph, predecessor, checkedSer);

										if (NoOfMatchedUnsatisfiedIn > 0) {
											// put the sampled predecessor into serSet
											if (!serQue.contains(predecessor)) {
												serQue.add(predecessor);
											}
										}
									}
								}
								p_counter++; // if not fully satisfied, keep sampling

							}
						}
					}
				}
			}
			sampled_pop.add(sampledIndi);

		}

		return sampled_pop;

	}

	// sampling function for sampling one individual requiring
	// re-normalization of the remaining after each sampling
	public int[] sampling(int[] numsToGenerate, double[] discreteProbabilities, Random random) {

		// sample node x with probability
		EnumeratedIntegerDistribution distribution = new EnumeratedIntegerDistribution(numsToGenerate,
				discreteProbabilities);

		distribution.reseedRandomGenerator(random.nextInt());

		return distribution.sample(1);
	}

	public List<WSCIndividual> getM_pop() {
		return m_pop;
	}

	public void setM_pop(List<WSCIndividual> m_pop) {
		this.m_pop = m_pop;
	}

}
