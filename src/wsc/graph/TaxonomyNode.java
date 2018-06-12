package wsc.graph;

import java.util.HashSet;
import java.util.Set;

import wsc.data.pool.Service;

/**
 * Represents a node in the input/output taxonomy used by the WSC dataset.
 *
 */
public class TaxonomyNode {

	public String concept;
	public Set<Service> servicesWithInput = new HashSet<Service>();
	public Set<Service> servicesWithOutput = new HashSet<Service>();

	public TaxonomyNode(String concept) {
		this.concept = concept;
	}
	
	

}
