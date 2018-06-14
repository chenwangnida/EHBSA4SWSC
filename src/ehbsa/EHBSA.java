package ehbsa;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.apache.commons.math3.distribution.EnumeratedIntegerDistribution;
import com.google.common.collect.Sets;

import wsc.data.pool.Service;
import wsc.graph.ServiceEdge;
import wsc.graph.ServiceGraph;
import wsc.graph.ServiceInput;
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
				m_node[ser.getServiceIndex()][j] = 0;
				sizeOfSDG++;
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

	public List<WSCIndividual> sampling4EHBSA(int sampleSize, Random random) {

		List<WSCIndividual> sampled_pop = new ArrayList<WSCIndividual>();

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

		// EHBSA/WO Sampling sampleSize numbers of individuals
		for (int no_sample = 0; no_sample < sampleSize; no_sample++) {
			// initial graph and its corresponding individual
			ServiceGraph graph = new ServiceGraph(ServiceEdge.class);
			graph.addVertex("startNode");
			graph.addVertex("endNode");

			WSCIndividual sampledIndi = new WSCIndividual();
			sampledIndi.setDagRepresentation(graph);

			// initial serSet with endNode
			Set<Service> serSet = new HashSet<Service>();

			// TO DO: set satisfaction 0 to inputs of all services

			// initial serSet with endSer
			serSet.add(WSCInitializer.endSer);

			// inital a candidate node list
			int[] c_candidates = new int[m_j];
			for (int m = 0; m < m_j; m++) {
				c_candidates[m] = m;
			}

			if (serSet.size() != 0) {
				for (Service s : serSet) {

					// set counter for number of unsatisfied inputs of s
					int noOfunsatisfiedIn = 0;

					// set the position counter
					int p_counter = 0;

					// reset satisfactions of service inputs to false
					for (ServiceInput serinput : s.getInputList()) {
						serinput.setSatified(false);
					}

					// set one dimension for sampling
					int j = s.getServiceIndex();

					while (true) {
						// sample one predecessor of current j
						double[] discreteProbabilities = new double[m_j - p_counter];

						// calculate probability and put them into proba[]
						double sum_proba = 0;
						for (int c : c_candidates) {
							if (c != -1) {
								sum_proba += m_node[c][j];
							}
						}

						int m = 0;

						for (int c : c_candidates) {
							// for -1 , we set 0 probability to its distribution
							if (m_node[c][j] == -1) {
								discreteProbabilities[m] = 0 / sum_proba;

							} else {
								discreteProbabilities[m] = m_node[c][j] / sum_proba;
							}
							m++;
						}

						// sample one predecessor from j
						int indexOfPredecessor = sampling(c_candidates, discreteProbabilities, random)[0];
						Service predecessor = WSCInitializer.Index2ServiceMap.get(indexOfPredecessor);

						// create an edge between predecessor and j, return no of matched unsatisfied
						// inputs if NoOfMatchedUnsatisfiedIn >0
						int NoOfMatchedUnsatisfiedIn = WSCInitializer.initialWSCPool.createEdge4TwoSer(graph,
								predecessor, s);

						if (NoOfMatchedUnsatisfiedIn > 0) {
							// put the sampled predecessor into serSet
							serSet.add(predecessor);

							// check number of unsatisfied inputs of service s
							int noOfUnsatisfiedIn = 0;
							for (ServiceInput in : s.getInputList()) {
								if (!in.isSatified()) {
									noOfUnsatisfiedIn++;
								}
							}

							if (noOfUnsatisfiedIn == 0) {// shall we move to next dimension for sampling
								break;
							}
						}
						p_counter++;

					}

					// all inputs are satisfied move j to next element in serSet, and remove current
					// one in

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
