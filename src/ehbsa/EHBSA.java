package ehbsa;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.jgrapht.experimental.dag.DirectedAcyclicGraph;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import wsc.data.pool.Service;
import wsc.graph.ServiceInput;
import wsc.owl.bean.OWLClass;
import wsc.problem.WSCIndividual;
import wsc.problem.WSCInitializer;

public class EHBSA {
	private int m_i; // size of i dimension
	private int m_j; // size of j dimension
	double[][] m_node; // a edge histogram matrix (EHM)
	private double m_bRatio;// a bias for EHM

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
			}
		}

		return m_node;
	}

	public final void setDefaultPara() {

		int sum_pop_edge = 0;
		m_pop.forEach(indi -> sum_pop_edge += indi.getEdgeSize());

		m_bRatio = 0.0002;// defined by users
		m_bRatio = (m_N * m_bRatio) / m_L; // bias
	}

	public List<WSCIndividual> sampling4EHBSA(double[][] m_node) {
		// To Do: set bias
		setDefaultPara();

		// add bias to only correct entries of NHM
		for (int i = 0; i < m_i; i++) {
			for (int j = 0; j < m_j; j++) {

				if (m_node[i][j] != -1) {
					m_node[i][j] += m_bRatio;
				}
			}
		}
		return null;

	}

	public List<WSCIndividual> getM_pop() {
		return m_pop;
	}

	public void setM_pop(List<WSCIndividual> m_pop) {
		this.m_pop = m_pop;
	}

}
