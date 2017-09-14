/*
#########################################################
#                                                       #
#  IBFSGraph -  Software for solving                    #
#               Maximum s-t Flow / Minimum s-t Cut      #
#               using the IBFS algorithm                #
#                                                       #
#  http://www.cs.tau.ac.il/~sagihed/ibfs/               #
#                                                       #
#  Haim Kaplan (haimk@cs.tau.ac.il)                     #
#  Sagi Hed (sagihed@post.tau.ac.il)                    #
#                                                       #
#########################################################

This software implements the IBFS (Incremental Breadth First Search) maximum flow algorithm from
	"Faster and More Dynamic Maximum Flow
	by Incremental Breadth-First Search"
	Andrew V. Goldberg, Sagi Hed, Haim Kaplan, Pushmeet Kohli,
	Robert E. Tarjan, and Renato F. Werneck
	In Proceedings of the 23rd European conference on Algorithms, ESA'15
	2015
and from
	"Maximum flows by incremental breadth-first search"
	Andrew V. Goldberg, Sagi Hed, Haim Kaplan, Robert E. Tarjan, and Renato F. Werneck.
	In Proceedings of the 19th European conference on Algorithms, ESA'11, pages 457-468.
	ISBN 978-3-642-23718-8
	2011

Copyright Haim Kaplan (haimk@cs.tau.ac.il) and Sagi Hed (sagihed@post.tau.ac.il)

###########
# LICENSE #
###########
This software can be used for research purposes only.
If you use this software for research purposes, you should cite the aforementioned papers
in any resulting publication and appropriately credit it.

If you require another license, please contact the above.

*/


#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <iostream>
#include "ibfs.h"


#define REMOVE_SIBLING(x, tmp) \
	{ (tmp) = &nodes[nodes[(x)->parent->head].firstSon]; \
	if ((tmp) == (x)) { \
		nodes[(x)->parent->head].firstSon = (x)->nextPtr; \
	} else { \
		for (; &nodes[(tmp)->nextPtr] != (x); (tmp) = &nodes[(tmp)->nextPtr]); \
		(tmp)->nextPtr = (x)->nextPtr; \
	} }

#define ADD_SIBLING(x, parentNode) \
	{ (x)->nextPtr = (parentNode)->firstSon; \
	(parentNode)->firstSon = (x - nodes); \
	}


IBFSGraph::IBFSGraph()
:prNodeBuckets(orphan3PassBuckets)
{
	arcIter = NULL;
	incList = NULL;
	incLen = incIteration = 0;
	numNodes = 0;
	uniqOrphansS = uniqOrphansT = 0;
	augTimestamp = 0;
	verbose = IBTEST;
	nodes = nodeEnd = NULL;
	topLevelS = topLevelT = 0;
	flow = 0;
	arcEnd = NULL;
	ptrs = NULL;
}


IBFSGraph::~IBFSGraph()
{
	delete []nodes;
	delete []arcEnd;
	orphanBuckets.free();
	orphan3PassBuckets.free();
	excessBuckets.free();
}

void IBFSGraph::initGraph()
{
	initGraphFast();
	topLevelS = topLevelT = 1;
}


void IBFSGraph::initSize(node_index_t numNodes)
{
	// compute allocation size
	unsigned long long nodeMemsize = (unsigned long long)sizeof(node_index_t)*(unsigned long long)(numNodes*3) +
			(IB_EXCESSES ? ((unsigned long long)sizeof(node_index_t)*(unsigned long long)(numNodes*2)) : 0);
	arcEnd = (Arc*) new char[nodeMemsize];
	memset(arcEnd, 0, (unsigned long long)sizeof(char)*nodeMemsize);

	// allocate nodes
//	if (verbose) {
//		fprintf(stdout, "c allocating nodes... \t [%lu MB]\n", (unsigned long)sizeof(Node)*(unsigned long)(numNodes+1) / (1<<20));
//		fflush(stdout);
//	}
	this->numNodes = numNodes;
	nodes = new Node[numNodes+1];
	memset(nodes, 0, sizeof(Node)*(numNodes+1));
	for (size_t i = 0; i < numNodes; ++i) {
		for (int j = 0; j < MAX_ARCS_PER_NODE; ++j) {
			nodes[i].arcs[j].head = NULL_INDEX;
		}
	}
	nodeEnd = nodes+numNodes;
	active0.init((node_index_t*)(arcEnd));
	activeS1.init((node_index_t*)(arcEnd) + numNodes);
	activeT1.init((node_index_t*)(arcEnd) + (2*numNodes));
	if (IB_EXCESSES) {
		for (size_t i = 0; i < numNodes*2; ++i) {
			((node_index_t*) arcEnd)[((size_t) numNodes)*3 + i] = NULL_INDEX;
		}
		ptrs = (node_index_t*)(arcEnd) + (3*numNodes);
		excessBuckets.init(nodes, ptrs, numNodes);
	}
	orphan3PassBuckets.init(nodes, numNodes);
	orphanBuckets.init(nodes, numNodes);

	// init members
	flow = 0;

	if (verbose) {
		fprintf(stdout, "c sizeof(ptr) = %d bytes\n", (int)sizeof(Node*));
		fprintf(stdout, "c sizeof(node) = %d bytes\n", (int)sizeof(Node));
		fprintf(stdout, "c sizeof(arc) = %d bytes\n", (int)sizeof(Arc));
	}
}


void IBFSGraph::initNodes()
{
	Node *x;
	for (x=nodes; x <= nodeEnd; x++) {
		x->nextPtr = NULL_INDEX;
		x->firstSon = NULL_INDEX;
		if (x->excess == 0) {
			x->label = 0;
			continue;
		}
		if (x->excess > 0) {
			x->label = 1;
			activeS1.add(CAST_TO_INDEX(x));
		} else {
			x->label = -1;
			activeT1.add(CAST_TO_INDEX(x));
		}
	}
}

void IBFSGraph::initGraphFast()
{
	initNodes();
}



// @ret: minimum orphan level
template<bool sTree> int IBFSGraph::augmentPath(Node *x, capacity_t push)
{
	Node *y;
	Arc *a;
	int orphanMinLevel = (sTree ? topLevelS : topLevelT) + 1;

	augTimestamp++;
	for (; ; x=&nodes[a->head])
	{
		if (x->excess) break;
		a = x->parent;
		Arc *reva = a->rev(nodes);
		if (sTree) {
			capacity_t rcap = a->getRCap() + push;
			a->setRCap(rcap);
			if (rcap > 0) {
				reva->setIsRevResidual(1);
			}
			reva->setRCap(reva->getRCap() - push);
		} else {
			capacity_t rcap = reva->getRCap() + push;
			reva->setRCap(rcap);
			if (rcap > 0) {
				a->setIsRevResidual(1);
			}
			a->setRCap(a->getRCap() - push);
		}

		// saturated?
		if ((sTree ? (reva->getRCap()) : (a->getRCap())) == 0)
		{
			if (sTree) a->setIsRevResidual(0);
			else reva->setIsRevResidual(0);
			REMOVE_SIBLING(x,y);
			orphanMinLevel = (sTree ? x->label : -x->label);
			orphanBuckets.add<sTree>(x);
		}
	}
	x->excess += (sTree ? -push : push);
	if (x->excess == 0) {
		orphanMinLevel = (sTree ? x->label : -x->label);
		orphanBuckets.add<sTree>(x);
	}
	flow += push;

	return orphanMinLevel;
}


// @ret: minimum level in which created an orphan
template<bool sTree> int IBFSGraph::augmentExcess(Node *x, capacity_t push)
{
	Node *y;
	Arc *a;
	int orphanMinLevel = (sTree ? topLevelS : topLevelT)+1;
	augTimestamp++;

	// start of loop
	//----------------
	// x 		  the current node along the path
	// a		  arc incoming into x
	// push 	  the amount of flow coming into x
	// a->resCap  updated with incoming flow already
	// x->excess  not updated with incoming flow yet
	//
	// end of loop
	//-----------------
	// x 		  the current node along the path
	// a		  arc outgoing from x
	// push 	  the amount of flow coming out of x
	// a->resCap  updated with outgoing flow already
	// x->excess  updated with incoming flow already
	while (sTree ? (x->excess <= 0) : (x->excess >= 0))
	{
		a = x->parent;
		Arc *reva = a->rev(nodes);

		// update excess and find next flow
		if ((sTree ? (reva->getRCap()) : (a->getRCap())) < (sTree ? (push-x->excess) : (x->excess+push))) {
			// some excess remains, node is an orphan
			x->excess += (sTree ? (reva->getRCap() - push) : (push-a->getRCap()));
			push = (sTree ? reva->getRCap() : a->getRCap());
		} else {
			// all excess is pushed out, node may or may not be an orphan
			push += (sTree ? -(x->excess) : x->excess);
			x->excess = 0;
		}

		// push flow
		// note: push != 0
		if (sTree) {
			capacity_t rcap = a->getRCap() + push;
			a->setRCap(rcap);
			if (rcap > 0) {
				reva->setIsRevResidual(1);
			}
			reva->setRCap(reva->getRCap() - push);
		} else {
			capacity_t rcap = reva->getRCap() + push;
			reva->setRCap(rcap);
			if (rcap > 0) {
				a->setIsRevResidual(1);
			}
			a->setRCap(a->getRCap() - push);
		}

		// saturated?
		if ((sTree ? (reva->getRCap()) : (a->getRCap())) == 0)
		{
			if (sTree) a->setIsRevResidual(0);
			else reva->setIsRevResidual(0);
			REMOVE_SIBLING(x,y);
			orphanMinLevel = (sTree ? x->label : -x->label);
			orphanBuckets.add<sTree>(x);
			if (x->excess) excessBuckets.incMaxBucket(sTree ? x->label : -x->label);
		}

		// advance
		// a precondition determines that the first node on the path is not in excess buckets
		// so only the next nodes may need to be removed from there
		x = &nodes[a->head];
		if (sTree ? (x->excess < 0) : (x->excess > 0)) excessBuckets.remove<sTree>(x);
	}

	// update the excess at the root
	if (push <= (sTree ? (x->excess) : -(x->excess))) flow += push;
	else flow += (sTree ? (x->excess) : -(x->excess));
	x->excess += (sTree ? (-push) : push);
	if (sTree ? (x->excess <= 0) : (x->excess >= 0)) {
		orphanMinLevel = (sTree ? x->label : -x->label);
		orphanBuckets.add<sTree>(x);
		if (x->excess) excessBuckets.incMaxBucket(sTree ? x->label : -x->label);
	}

	return orphanMinLevel;
}


template<bool sTree> void IBFSGraph::augmentExcesses()
{
	Node *x;
	int minOrphanLevel;
	int adoptedUpToLevel = excessBuckets.maxBucket;

	if (!excessBuckets.empty())
	for (; excessBuckets.maxBucket != (excessBuckets.minBucket-1); excessBuckets.maxBucket--)
	while ((x=excessBuckets.popFront(excessBuckets.maxBucket)) != NULL)
	{
		minOrphanLevel = augmentExcess<sTree>(x, 0);
		// if we did not create new orphans
		if (adoptedUpToLevel < minOrphanLevel) minOrphanLevel = adoptedUpToLevel;
		adoption<sTree>(minOrphanLevel, false);
		adoptedUpToLevel = excessBuckets.maxBucket;
	}
	excessBuckets.reset();
	if (orphanBuckets.maxBucket != 0) adoption<sTree>(adoptedUpToLevel+1, true);
	// free 3pass orphans
	while ((x=excessBuckets.popFront(0)) != NULL) orphanFree<sTree>(x);
}


void IBFSGraph::augment(Arc *bridge)
{
	Node *x, *y;
	Arc *a;
	capacity_t bottleneck, bottleneckT, bottleneckS;
	int minOrphanLevel;
	bool forceBottleneck;

	// must compute forceBottleneck once, so that it is constant throughout this method
	forceBottleneck = (IB_EXCESSES ? false : true);
	if (IB_BOTTLENECK_ORIG && IB_EXCESSES)
	{
		/*
		// limit by end nodes excess
		bottleneck = bridge->rCap;
		if (bridge->head->excess != 0 && -(bridge->head->excess) < bottleneck) {
			bottleneck = -(bridge->head->excess);
		}
		if (bridge->rev(nodes)->head->excess != 0 && bridge->rev(nodes)->head->excess < bottleneck) {
			bottleneck = bridge->rev(nodes)->head->excess;
		}
		 */
	}
	else
	{
		bottleneck = bottleneckS = bridge->getRCap();
		if (bottleneck != 1) {
			for (x=&nodes[bridge->rev(nodes)->head]; ; x=&nodes[a->head])
			{
				if (x->excess) break;
				a = x->parent;
				if (bottleneckS > a->rev(nodes)->getRCap()) {
					bottleneckS = a->rev(nodes)->getRCap();
				}
			}
			if (bottleneckS > x->excess) {
				bottleneckS = x->excess;
			}
			if (IB_EXCESSES && x->label != 1) forceBottleneck = true;
			if (x == &nodes[bridge->rev(nodes)->head]) bottleneck = bottleneckS;
		}

		if (bottleneck != 1) {
			bottleneckT = bridge->getRCap();
			for (x=&nodes[bridge->head]; ; x=&nodes[a->head])
			{
				if (x->excess) break;
				a = x->parent;
				if (bottleneckT > a->getRCap()) {
					bottleneckT = a->getRCap();
				}
			}
			if (bottleneckT > (-x->excess)) {
				bottleneckT = (-x->excess);
			}
			if (IB_EXCESSES && x->label != -1) forceBottleneck = true;
			if (x == &nodes[bridge->head] && bottleneck > bottleneckT) bottleneck = bottleneckT;

			if (forceBottleneck) {
				if (bottleneckS < bottleneckT) bottleneck = bottleneckS;
				else bottleneck = bottleneckT;
			}
		}
	}

	// stats
	if (IBSTATS) {
		int augLen = (-(nodes[bridge->head].label)-1 + nodes[bridge->rev(nodes)->head].label-1 + 1);
	}

	Arc *revbridge = bridge->rev(nodes);

	// augment connecting arc
	capacity_t rcap = revbridge->getRCap() + bottleneck;
	revbridge->setRCap(rcap);
	if (rcap > 0) {
		bridge->setIsRevResidual(1);
	}
	bridge->setRCap(bridge->getRCap() - bottleneck);
	if (bridge->getRCap() == 0) {
		revbridge->setIsRevResidual(0);
	}
	flow -= bottleneck;

	// augment T
	x = &nodes[bridge->head];
	if (!IB_EXCESSES || bottleneck == 1 || forceBottleneck) {
		minOrphanLevel = augmentPath<false>(x, bottleneck);
		adoption<false>(minOrphanLevel, true);
	} else {
		minOrphanLevel = augmentExcess<false>(x, bottleneck);
		adoption<false>(minOrphanLevel, false);
		augmentExcesses<false>();
	}

	// augment S
	x = &nodes[bridge->rev(nodes)->head];
	if (!IB_EXCESSES || bottleneck == 1 || forceBottleneck) {
		minOrphanLevel = augmentPath<true>(x, bottleneck);
		adoption<true>(minOrphanLevel, true);
	} else {
		minOrphanLevel = augmentExcess<true>(x, bottleneck);
		adoption<true>(minOrphanLevel, false);
		augmentExcesses<true>();
	}
}




template<bool sTree> void IBFSGraph::adoption(int fromLevel, bool toTop)
{
	Node *x, *y;
	node_index_t y_index;
	node_index_t z;
	register Arc *a;
	Arc *aEnd;
	int threePassLevel;
	int minLabel, numOrphans, numOrphansUniq;
	int level;

	threePassLevel=0;
	numOrphans=0;
	numOrphansUniq=0;
	for (level = fromLevel;
		level <= orphanBuckets.maxBucket &&
		(!IB_EXCESSES || toTop || threePassLevel || level <= excessBuckets.maxBucket);
		level++)
	while ((x=orphanBuckets.popFront(level)) != NULL)
	{
		numOrphans++;
		if (x->lastAugTimestamp != augTimestamp) {
			x->lastAugTimestamp = augTimestamp;
			if (sTree) uniqOrphansS++;
			else uniqOrphansT++;
			numOrphansUniq++;
		}
		if (IB_HYBRID_ADOPTION && threePassLevel == 0 && numOrphans >= 3*numOrphansUniq) {
			// switch to 3pass
			threePassLevel = 1;
		}

		//
		// check for same level connection
		//
		if (x->isParentCurr) {
			a = x->parent;
		} else {
			a = (&x->arcs[0]);
			x->isParentCurr = 1;
		}
		x->parent = NULL;
		aEnd = (&x->arcs[x->arcsDegree()]);
		if (x->label != (sTree ? 1 : -1))
		{
			minLabel = x->label - (sTree ? 1 : -1);
			for (; a != aEnd; a++)
			{
				y = &nodes[a->head];
				if ((sTree ? a->getIsRevResidual() : a->getRCap()) != 0 && y->label == minLabel)
				{
					x->parent = a;
					ADD_SIBLING(x,y);
					break;
				}
			}
		}
		if (x->parent != NULL) {
			if (IB_EXCESSES && x->excess) excessBuckets.add<sTree>(x);
			continue;
		}

		//
		// on the top level there is no need to relabel
		//
		if (x->label == (sTree ? topLevelS : -topLevelT)) {
			orphanFree<sTree>(x);
			continue;
		}

		//
		// give up on same level - relabel it!
		// (1) create orphan sons
		//
		for (y_index=x->firstSon; y_index != NULL_INDEX; y_index=z)
		{
			y=&nodes[y_index];
			z=y->nextPtr;
			if (IB_EXCESSES && y->excess) excessBuckets.remove<sTree>(y);
			orphanBuckets.add<sTree>(y);
		}
		x->firstSon = NULL_INDEX;

		//
		// (2) 3pass relabeling: move to buckets structure
		//
		if (threePassLevel) {
			x->label += (sTree ? 1 : -1);
			orphan3PassBuckets.add<sTree>(x);
			if (threePassLevel == 1) {
				threePassLevel = level+1;
			}
			continue;
		}

		//
		// (2) relabel: find the lowest level parent
		//
		minLabel = (sTree ? topLevelS : -topLevelT);
		if (x->label != minLabel) for (a=(&x->arcs[0]); a != aEnd; a++)
		{
			y = &nodes[a->head];
			if ((sTree ? a->getIsRevResidual() : a->getRCap()) &&
				// y->label != 0 ---> holds implicitly
				(sTree ? (y->label > 0) : (y->label < 0)) &&
				(sTree ? (y->label < minLabel) : (y->label > minLabel)))
			{
				minLabel = y->label;
				x->parent = a;
				if (minLabel == x->label) break;
			}
		}

		//
		// (3) relabel onto new parent
		//
		if (x->parent != NULL) {
			x->label = minLabel + (sTree ? 1 : -1);
			ADD_SIBLING(x, &nodes[x->parent->head]);
			// add to active list of the next growth phase
			if (sTree) {
				if (x->label == topLevelS) activeS1.add(CAST_TO_INDEX(x));
			} else {
				if (x->label == -topLevelT) activeT1.add(CAST_TO_INDEX(x));
			}
			if (IB_EXCESSES && x->excess) excessBuckets.add<sTree>(x);
		} else {
			orphanFree<sTree>(x);
		}
	}
	if (level > orphanBuckets.maxBucket) orphanBuckets.maxBucket=0;

	if (threePassLevel) {
		adoption3Pass<sTree>(threePassLevel);
	}
}

template <bool sTree> void IBFSGraph::adoption3Pass(int minBucket)
{
	Arc *a, *aEnd;
	Node *x, *y;
	int minLabel, destLabel;

	for (int level=minBucket; level <= orphan3PassBuckets.maxBucket; level++)
	while ((x = orphan3PassBuckets.popFront(level)) != NULL)
	{
		aEnd = (&x->arcs[x->arcsDegree()]);

		// pass 2: find lowest level parent
		if (x->parent == NULL) {
			minLabel = (sTree ? topLevelS : -topLevelT);
			destLabel = x->label - (sTree ? 1 : -1);
			for (a=(&x->arcs[0]); a != aEnd; a++) {
				y = &nodes[a->head];
				if ((sTree ? a->getIsRevResidual() : a->getRCap()) &&
					((sTree ? (y->excess > 0) : (y->excess < 0)) || y->parent != NULL) &&
					(sTree ? (y->label > 0) : (y->label < 0)) &&
					(sTree ? (y->label < minLabel) : (y->label > minLabel)))
				{
					x->parent = a;
					if ((minLabel = y->label) == destLabel) break;
				}
			}
			if (x->parent == NULL) {
				x->label = 0;
				if (IB_EXCESSES && x->excess) excessBuckets.add<sTree>(x);
				continue;
			}
			x->label = minLabel + (sTree ? 1 : -1);
			if (x->label != (sTree ? level : -level)) {
				orphan3PassBuckets.add<sTree>(x);
				continue;
			}
		}

		// pass 3: lower potential sons and/or find first parent
		if (x->label != (sTree ? topLevelS : -topLevelT))
		{
			minLabel = x->label + (sTree ? 1 : -1);
			for (a=(&x->arcs[0]); a != aEnd; a++) {
				y = &nodes[a->head];

				// lower potential sons
				if ((sTree ? a->getRCap() : a->getIsRevResidual()) &&
					(y->label == 0 ||
					(sTree ? (minLabel < y->label) : (minLabel > y->label))))
				{
					if (y->label != 0) orphan3PassBuckets.remove<sTree>(y);
					else if (IB_EXCESSES && y->excess) excessBuckets.remove<sTree>(y);
					y->label = minLabel;
					y->parent = a->rev(nodes);
					orphan3PassBuckets.add<sTree>(y);
				}
			}
		}

		// relabel onto new parent
		ADD_SIBLING(x, &nodes[x->parent->head]);
		x->isParentCurr = 0;
		if (IB_EXCESSES && x->excess) excessBuckets.add<sTree>(x);

		// add to active list of the next growth phase
		if (sTree) {
			if (x->label == topLevelS) activeS1.add(CAST_TO_INDEX(x));
		} else {
			if (x->label == -topLevelT) activeT1.add(CAST_TO_INDEX(x));
		}
	}

	orphan3PassBuckets.maxBucket = 0;
}


template<bool dirS> void IBFSGraph::growth()
{
	Node *x, *y;
	Arc *a, *aEnd;

	for (node_index_t *active=active0.list; active != (active0.list + active0.len); active++)
	{
		// get active node
		x = CAST_TO_PTR(*active);

		// node no longer at level
		if (x->label != (dirS ? (topLevelS-1): -(topLevelT-1))) {
			continue;
		}

		aEnd = (&x->arcs[x->arcsDegree()]);
		for (a=(&x->arcs[0]); a != aEnd; a++)
		{
			if ((dirS ? a->getRCap() : a->getIsRevResidual()) == 0) continue;
			y = &nodes[a->head];
			if (y->label == 0)
			{
				// grow node x (attach y)
				y->isParentCurr = 0;
				y->label = x->label + (dirS ? 1 : -1);
				y->parent = a->rev(nodes);
				ADD_SIBLING(y, x);
				if (dirS) activeS1.add(CAST_TO_INDEX(y));
				else activeT1.add(CAST_TO_INDEX(y));
			}
			else if (dirS ? (y->label < 0) : (y->label > 0))
			{
				// augment
				augment(dirS ? a : (a->rev(nodes)));
				if (x->label != (dirS ? (topLevelS-1) : -(topLevelT-1))) {
					break;
				}
				if (dirS ? (a->getRCap()) : (a->getIsRevResidual())) a--;
			}
		}
	}
	active0.clear();
}

template<bool sTree> void IBFSGraph::augmentIncrements()
{
	Node *x, *y;
	Node **end = incList+incLen;
	int minOrphanLevel = 1<<30;

	for (Node **inc=incList; inc != end; inc++)
	{
		x = (*inc);
		if (!x->isIncremental || (sTree ? (x->label < 0) : (x->label > 0))) continue;
		x->isIncremental = 0;
		if (x->label == 0)
		{
			//**** new root from outside the tree
			if (!x->excess) continue;
			x->isParentCurr = 0;
			if (x->excess > 0) {
				x->label = topLevelS;
				activeS1.add(CAST_TO_INDEX(x));
			} else if (x->excess < 0) {
				x->label = -topLevelT;
				activeT1.add(CAST_TO_INDEX(x));
			}
		}
		else if ((sTree ? (x->excess <= 0) : (x->excess >= 0)) &&
				(!x->parent || !(sTree ? x->parent->getIsRevResidual() : x->parent->getRCap())))
		{
			//**** new orphan
			if (x->parent) REMOVE_SIBLING(x,y);
			if ((sTree ? x->label : -x->label) < minOrphanLevel) {
				minOrphanLevel = (sTree ? x->label : -x->label);
			}
			orphanBuckets.add<sTree>(x);
			if (x->excess) excessBuckets.incMaxBucket(sTree ? x->label : -x->label);
		}
		else if (sTree ? (x->excess < 0) : (x->excess > 0))
		{
			//**** new deficit/excess to empty
			excessBuckets.add<sTree>(x);
		}
		else if (x->excess && x->parent)
		{
			//**** new root
			REMOVE_SIBLING(x,y);
			x->parent = NULL;
			x->isParentCurr = 0;
		}
	}
	if (orphanBuckets.maxBucket != 0) adoption<sTree>(minOrphanLevel, false);
	augmentExcesses<sTree>();
}


IBFSGraph::capacity_t IBFSGraph::computeMaxFlow()
{
	return computeMaxFlow(true, false);
}

IBFSGraph::capacity_t IBFSGraph::computeMaxFlow(bool allowIncrements)
{
	return computeMaxFlow(true, allowIncrements);
}

IBFSGraph::capacity_t IBFSGraph::computeMaxFlow(bool initialDirS, bool allowIncrements)
{
	// incremental?
	if (incIteration >= 1 && incList != NULL) {
		augmentIncrements<true>();
		augmentIncrements<false>();
		incList = NULL;
	}

	//
	// IBFS
	//
	bool dirS = initialDirS;
	while (true)
	{
		// BFS level
		if (dirS) {
			ActiveList::swapLists(&active0, &activeS1);
			topLevelS++;
		} else {
			ActiveList::swapLists(&active0, &activeT1);
			topLevelT++;
		}
		orphanBuckets.allocate((topLevelS > topLevelT) ? topLevelS : topLevelT);
		orphan3PassBuckets.allocate((topLevelS > topLevelT) ? topLevelS : topLevelT);
		if (IB_EXCESSES) excessBuckets.allocate((topLevelS > topLevelT) ? topLevelS : topLevelT);
		if (dirS) growth<true>();
		else growth<false>();
		if (IBTEST) {
			fprintf(stdout, "dirS=%d aug=%d   S %d / T %d   flow=%f\n",
					dirS, augTimestamp, uniqOrphansS, uniqOrphansT, flow);
			fflush(stdout);
		}

		// switch to next level
		if (!allowIncrements && (activeS1.len == 0 || activeT1.len == 0)) break;
		if (activeS1.len == 0 && activeT1.len == 0) break;
		if (activeT1.len == 0) dirS=true;
		else if (activeS1.len == 0) dirS=false;
		else if (!IB_ALTERNATE_SMART && dirS) dirS = false;
		else if (IB_ALTERNATE_SMART && uniqOrphansT == uniqOrphansS && dirS) dirS=false;
		else if (IB_ALTERNATE_SMART && uniqOrphansT < uniqOrphansS) dirS=false;
		else dirS=true;
	}

	incIteration++;
	return flow;
}
