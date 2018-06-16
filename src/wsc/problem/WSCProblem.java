package wsc.problem;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;

import java.util.List;

import ehbsa.EHBSA;
import wsc.graph.ServiceGraph;

public class WSCProblem {
	public static void main(String[] args) throws IOException {

		if (args.length != 5) {
			System.out.println("missing arguments!");
			return;
		}

		WSCInitializer.initialisationStartTime = System.currentTimeMillis();

		WSCInitializer init = new WSCInitializer(args[0], args[1], args[2], args[3], Long.valueOf(args[4]));
		WSCGraph graGenerator = new WSCGraph();
		WSCEvaluation eval = new WSCEvaluation();

		WSCProblem p = new WSCProblem();
		p.EHBSASolver(graGenerator, eval);

	}

	// The main entry to NHBSASolver.
	public void EHBSASolver(WSCGraph graGenerator, WSCEvaluation eval) {

		long initialization = System.currentTimeMillis() - WSCInitializer.initialisationStartTime;

		List<WSCIndividual> population = new ArrayList<WSCIndividual>();
		// entry to NHBSA
		EHBSA ehbsa = new EHBSA(WSCInitializer.dimension_size, WSCInitializer.dimension_size);

		double[][] m_node = ehbsa.initialEHM();

		// random initalize one double size population solutions
		while (population.size() < WSCInitializer.population_size) {
			WSCIndividual individual = new WSCIndividual();
			// graph-based representation
			ServiceGraph graph = graGenerator.generateGraph();
			individual.setDagRepresentation(graph);

			eval.aggregationAttribute(individual, graph);
			eval.calculateFitness(individual);
			population.add(individual);
		}

		// entry to learn the matrix and sampling individuals
		int iteration = 0;
		while (iteration < WSCInitializer.MAX_NUM_ITERATIONS) {
			long startTime = System.currentTimeMillis();
			System.out.println("GENERATION " + iteration);

			// sort the individuals according to the fitness
			Collections.sort(population);

			// Debug Test
			for (WSCIndividual indi : population) {
				if (indi.getDagRepresentation().containsEdge("startNode", "serv212250832")
						&& indi.getDagRepresentation().containsEdge("serv212250832", "serv1805915141")
						&& indi.getDagRepresentation().containsEdge("serv1805915141", "serv1113231355")
						&& indi.getDagRepresentation().containsEdge("serv1113231355", "serv1182663588")
						&& indi.getDagRepresentation().containsEdge("serv1182663588", "serv559411997")
						&& indi.getDagRepresentation().containsEdge("serv559411997", "serv2014211840")
						&& indi.getDagRepresentation().containsEdge("serv2014211840", "serv1321528054")
						&& indi.getDagRepresentation().containsEdge("serv1321528054", "serv628844230")
						&& indi.getDagRepresentation().containsEdge("serv628844230", "serv2083644073")
						&& indi.getDagRepresentation().containsEdge("serv2083644073", "serv1460392520")
						&& indi.getDagRepresentation().containsEdge("serv1460392520", "endNode")
						&& indi.getDagRepresentation().vertexSet().size() == 12) {

					System.out.println(indi.getFitness() + ";" + indi.getDagRepresentation());
				}
			}

			// update best individual so far
			if (iteration == 0) {
				WSCInitializer.bestFitnessSoFar.add(population.get(0));
			} else {
				if (WSCInitializer.bestFitnessSoFar.get(iteration - 1).fitness < population.get(0).fitness) {
					WSCInitializer.bestFitnessSoFar.add(population.get(0));
				} else {
					WSCInitializer.bestFitnessSoFar.add(WSCInitializer.bestFitnessSoFar.get(iteration - 1));
				}
			}

			// select first half population into matrix and archive
			List<WSCIndividual> archive = new ArrayList<WSCIndividual>();
			for (int m = 0; m < WSCInitializer.population_size / 2; m++) {
				archive.add(population.get(m));
			}
			// set archive as population for learning EHM
			ehbsa.setM_pop(archive);

			// Learn EHBSA with initial EHM
			ehbsa.learnEHMfromPop();

			// sample new candidate solutions from EHM
			List<WSCIndividual> pop_updated = ehbsa.sampling4EHBSA(WSCInitializer.population_size / 2,
					WSCInitializer.random);

			population.clear();

			// add another half number of pop to population
			population.addAll(archive);

			// add the population with pop_updated
			for (int m = 0; m < pop_updated.size(); m++) {
				WSCIndividual id_updated = pop_updated.get(m);
				eval.aggregationAttribute(id_updated, id_updated.getDagRepresentation());
				eval.calculateFitness(id_updated);
				population.add(id_updated);
			}
			WSCInitializer.initTime.add(initialization);
			initialization = (long) 0.0;
			WSCInitializer.time.add(System.currentTimeMillis() - startTime);

			iteration += 1;
		}

		writeLogs();

	}

	public void writeLogs() {
		try {
			FileWriter writer = new FileWriter(new File(WSCInitializer.logName));
			for (int i = 0; i < WSCInitializer.bestFitnessSoFar.size(); i++) {
				writer.append(String.format("%d %d %d %f\n", i, WSCInitializer.initTime.get(i),
						WSCInitializer.time.get(i), WSCInitializer.bestFitnessSoFar.get(i).fitness));

				// test print out all individuals
				// writer.append("\n");
				// writer.append(WSCInitializer.bestFitnessSoFar.get(i)
				// .getStrRepresentation());

			}
			writer.append(WSCInitializer.bestFitnessSoFar.get(WSCInitializer.bestFitnessSoFar.size() - 1)
					.getStrRepresentation());
			writer.append("\n");

			// print out the entropy for obeservation
			// for (int i = 0; i < NHBSA.discountRate4Gen.size(); i++) {
			// writer.append(String.format("%s\n", NHBSA.discountRate4Gen.get(i)));
			// }
			//
			// LineChart lc = new LineChart();
			// lc.createLineChart(NHBSA.entropy4Gen, NHBSA.discountRate4Gen);

			writer.close();

		} catch (IOException e) {
			e.printStackTrace();
		}
	}

}
