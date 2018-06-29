package ehbsa;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Random;
import java.util.Set;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.traverse.BreadthFirstIterator;
import org.jgrapht.traverse.GraphIterator;
import org.jgrapht.graph.DirectedWeightedSubgraph;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import wsc.InitialWSCPool;
import wsc.data.pool.Service;
import wsc.graph.ServiceEdge;
import wsc.graph.ServiceGraph;
import wsc.graph.ServiceInput;
import wsc.graph.ServiceOutput;
import wsc.problem.WSCEvaluation;
import wsc.problem.WSCGraph;
import wsc.problem.WSCIndividual;
import wsc.problem.WSCInitializer;

public class LocalSearch {

	// local search for random one-point swap for Top 1 and 5 from groups by
	// fitness
	// distribution with 20
	// neighbors
	public List<WSCIndividual> subGraphBasedSamplingfromGroups(List<WSCIndividual> population, EHBSA ehbsa,
			Random random, WSCGraph graGenerator, WSCEvaluation eval) {
		int split = 0;

		Collections.sort(population);
		List<WSCIndividual> solutions4LS = new ArrayList<WSCIndividual>();

		// obtain individuals for selection
		solutions4LS.add(population.get(0));

		final double fitnessSize = (population.get(0).fitness - population.get(population.size() - 1).fitness) / 5;

		List<WSCIndividual> partition1 = new ArrayList<WSCIndividual>();
		List<WSCIndividual> partition2 = new ArrayList<WSCIndividual>();
		List<WSCIndividual> partition3 = new ArrayList<WSCIndividual>();
		List<WSCIndividual> partition4 = new ArrayList<WSCIndividual>();
		List<WSCIndividual> partition5 = new ArrayList<WSCIndividual>();

		for (int i = 0; i < population.size(); i++) {
			WSCIndividual indi = population.get(i);
			if (indi.getFitness() >= (population.get(0).fitness - fitnessSize)) {
				partition1.add(population.get(i));
			} else if (indi.getFitness() >= (population.get(0).fitness - fitnessSize * 2)) {
				partition2.add(population.get(i));
			} else if (indi.getFitness() >= (population.get(0).fitness - fitnessSize * 3)) {
				partition3.add(population.get(i));
			} else if (indi.getFitness() >= (population.get(0).fitness - fitnessSize * 4)) {
				partition4.add(population.get(i));
			} else {
				partition5.add(population.get(i));
			}
		}

		// need to fix the bug

		if (partition1.size() != 0) {
			solutions4LS.add(partition1.get(random.nextInt(partition1.size())));
		}

		if (partition2.size() != 0) {
			solutions4LS.add(partition2.get(random.nextInt(partition2.size())));
		}

		if (partition3.size() != 0) {
			solutions4LS.add(partition3.get(random.nextInt(partition3.size())));
		}
		if (partition4.size() != 0) {
			solutions4LS.add(partition4.get(random.nextInt(partition4.size())));
		}
		if (partition5.size() != 0) {
			solutions4LS.add(partition5.get(random.nextInt(partition5.size())));
		}

		List<WSCIndividual> solutions4LSWithoutDuplicates = Lists.newArrayList(Sets.newHashSet(solutions4LS));

		for (WSCIndividual indi : solutions4LSWithoutDuplicates) {

			List<WSCIndividual> indi_neigbouring = new ArrayList<WSCIndividual>();

			for (int nOfls = 0; nOfls < WSCInitializer.numOfLS5Group; nOfls++) {
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

				// obtain the selected vertex of the individual

				WSCIndividual indi_temp = new WSCIndividual();

				// obtain all vertex from indi
				List<String> allVertex = Lists.newArrayList(indi.getDagRepresentation().vertexSet());

				int selectedVertex = random.nextInt(allVertex.size());// between 0 (inclusive) and
				// size (exclusive)

				String selectedServ = allVertex.get(selectedVertex);

				// breath first search get all its successors
				Set<String> predecessorSers = new HashSet<String>();
				GraphIterator<String, ServiceEdge> iterator = new BreadthFirstIterator<String, ServiceEdge>(
						indi.getDagRepresentation(), selectedServ);
				while (iterator.hasNext()) {
					// Also add input to current node and all its children nodes
					String succesor = iterator.next();
					// graph.addVertex(succesor);
					// Create a service queue, and put it the queue
					predecessorSers.add(succesor);
				}
				DirectedWeightedSubgraph<String, ServiceEdge> subGraph = new DirectedWeightedSubgraph<String, ServiceEdge>(
						indi.getDagRepresentation(), predecessorSers);

				// identify services not fully satisfied or not satisfied
				Set<Service> serSet = new HashSet<Service>();

				for (String ver : subGraph.vertexSet()) {
					if (subGraph.incomingEdgesOf(ver) == null) {
						serSet.add(WSCInitializer.serviceMap.get(ver));
					} else {
						if (indi.getDagRepresentation().incomingEdgesOf(ver).size() > subGraph.incomingEdgesOf(ver)
								.size()) {
							serSet.add(WSCInitializer.serviceMap.get(ver));
						}
					}

				}

				// update services inputs that are partially satisfied in the subGraph and put
				// into a new Graph

				ServiceGraph graph = new ServiceGraph(ServiceEdge.class);
				graph.addVertex("endNode");

				for (Service ver : serSet) {
					for (ServiceEdge serEdge : subGraph.incomingEdgesOf(ver.getServiceID())) {
						String source = (String) serEdge.getSource();
						if (source != null) {
							WSCInitializer.initialWSCPool.createEdge4TwoSer(graph,
									WSCInitializer.serviceMap.get(source), ver);
						}
					}
				}

				// sample from a given queue and unfinished graph
				ServiceGraph sampledDAG = ehbsa.samplingBasedOnSubGraph(random, graph, serSet);

				indi_temp.setDagRepresentation(sampledDAG);

				// update those inputs of this unsatisfied service
				// evaluate updated updated_graph
				eval.aggregationAttribute(indi_temp, sampledDAG);
				eval.calculateFitness(indi_temp);
				// add
				indi_neigbouring.add(indi_temp);
			}
		}

		// Collections.sort(indi_neigbouring);

		// if the best of neighbour solutions is better than the parent

		// if (indi_neigbouring.get(0).fitness > indi.fitness) {
		// population.set(population.indexOf(indi), indi_neigbouring.get(0));
		// }

		return population;
	}

}
