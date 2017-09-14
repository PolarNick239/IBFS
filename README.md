# IBFS with lower memory consumption and floating point capacity support

This is the modified version of IBFS solver for max-flow min-cut problem:

 - Lower memory consumption by using ```unsigned int``` instead of pointers (can easily be switched to ```size_t``` by ```node_index_t``` typedef)
 - Capacity type changed from ```int``` to ```float``` (can easilty be switched to double/int/etc by ```capacity_t``` typedef)
 - Number of edges from each node limited to ```MAX_ARCS_PER_NODE``` (MAX_ARCS_PER_NODE=4 tested - useful for Delaunay tetrahedralization, dinamic number of edges can be recovered)
 - Some functions were removed because I didn't need them, but they can be recovered

Original IBFS site - http://www.cs.tau.ac.il/~sagihed/ibfs/

# Papers

See

"Faster and More Dynamic Maximum Flow by Incremental Breadth-First Search"
Andrew V. Goldberg, Sagi Hed, Haim Kaplan, Pushmeet Kohli, Robert E. Tarjan, and Renato F. Werneck

"Maximum Flows By Incremental Breadth-First Search"
A.V. Goldberg, S.Hed, H. Kaplan, R.E. Tarjan, and R.F. Werneck

# License

This software can be used for research purposes only.

If you use this software for research purposes, you should cite the aforementioned papers in any resulting publication and appropriately credit it.

If you require another license, please contact authors as described on site of original IBFS [site](http://www.cs.tau.ac.il/~sagihed/ibfs/code.html). **But note that the price is VERY high.**
