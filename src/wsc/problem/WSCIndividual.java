package wsc.problem;

import java.util.ArrayList;
import java.util.List;

import org.jgrapht.experimental.dag.DirectedAcyclicGraph;
import org.jgrapht.graph.DefaultEdge;

import wsc.graph.ServiceGraph;

public class WSCIndividual implements Comparable<WSCIndividual> {

	private String strRepresentation; // a string of graph-based representation
	private ServiceGraph dagRepresentation;
	private int edgeSize;
	private double availability;
	private double reliability;
	private double time;
	private double cost;
	private double matchingType;
	private double semanticDistance;

	public double fitness = 0.0; // The higher, the fitterSSSS

	@Override
	public int compareTo(WSCIndividual o) {
		return Double.compare(o.fitness, this.fitness);
	}

	public double getAvailability() {
		return availability;
	}

	public void setAvailability(double availability) {
		this.availability = availability;
	}

	public double getReliability() {
		return reliability;
	}

	public void setReliability(double reliability) {
		this.reliability = reliability;
	}

	public double getTime() {
		return time;
	}

	public void setTime(double time) {
		this.time = time;
	}

	public double getCost() {
		return cost;
	}

	public void setCost(double cost) {
		this.cost = cost;
	}

	public double getMatchingType() {
		return matchingType;
	}

	public void setMatchingType(double matchingType) {
		this.matchingType = matchingType;
	}

	public double getSemanticDistance() {
		return semanticDistance;
	}

	public void setSemanticDistance(double semanticDistance) {
		this.semanticDistance = semanticDistance;
	}

	public double getFitness() {
		return fitness;
	}

	public void setFitness(double fitness) {
		this.fitness = fitness;
	}

	public ServiceGraph getDagRepresentation() {
		return dagRepresentation;
	}

	public void setDagRepresentation(ServiceGraph dagRepresentation) {
		this.dagRepresentation = dagRepresentation;
	}

	public String getStrRepresentation() {
		return strRepresentation;
	}

	public void setStrRepresentation(String strRepresentation) {
		this.strRepresentation = strRepresentation;
	}

	public int getEdgeSize() {
		return edgeSize;
	}

	public void setEdgeSize(int edgeSize) {
		this.edgeSize = edgeSize;
	}

}
