package wsc.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import wsc.data.pool.Service;

/**
 * Represents a node in the input/output taxonomy used by the WSC dataset.
 *
 */
public class TaxonomyNode {

	public String concept;
	public List<Service> servicesWithInput = new ArrayList<Service>();
	public List<Service> servicesWithOutput = new ArrayList<Service>();

	public TaxonomyNode(String concept) {
		this.concept = concept;
	}

}
