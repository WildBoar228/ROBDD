from cProfile import label
import collections
from distutils.command.build import build
from functools import cache
from math import exp
import random
import weakref
import boolfunc
import pydot
from IPython.display import Image, display
import urp
import pcn


class BDDNode:
    """ Class for a bdd node"""
    # Defining the key for zero and one nodes
    BDDNODEZEROKEY = (-1, id(None), id(None))
    BDDNODEONEKEY = (-2, id(None), id(None))

    def __init__(self, exp, var):
        """ constructor for BDDNode class """
        self.exp = exp
        self.var = var
        self.lo = None
        self.hi = None

    @staticmethod
    def getNodeZero(numVars):
        """ returns the zero node """
        # the var for zero node is made -1
        exp = boolfunc.Expression.getEqnZero(numVars)
        return BDDNode(exp, -1)

    @staticmethod
    def getNodeOne(numVars):
        """ returns the one node """
        # the var for one node is made -2
        exp = boolfunc.Expression.getEqnOne(numVars)
        return BDDNode(exp, -2)

    def getKey(self):
        """ returns the key for the node """
        return (self.var, id(self.lo), id(self.hi))

    def __str__(self) -> str:
        """ returns the string representation of the node """
        rep = list()
        rep.append(f"id:{id(self)}")
        rep.append(f"var:{self.var}")
        rep.append(f"exp:{self.exp}")
        rep.append(f"lo:{id(self.lo)}")
        rep.append(f"hi:{id(self.lo)}")
        return "\n".join(rep)

    def __repr__(self) -> str:
        """ returns the string representation of the node """
        return self.__str__()

    def _getUid(self):
        """returns the UID for a node"""
        uid = f"var->{self.var}\nid->{id(self)}\nlo->{id(self.lo)}    hi->{id(self.hi)}"
        return uid

    def getLabel(self):
        """ returns the label for the node """

        # label is 0 if val is -1
        if self.var == -1:
            label = "0"
        # label is 1 if val is -2
        elif self.var == -2:
            label = "1"
        # label is the variable in expression
        else:
            label = f"X{self.var}"
        return label

    def displayGraph(self):
        """ displays the graph """
        img = self.getPng()
        display(img)

    def getPng(self):
        """ returns the png image of the graph """
        self.graph = pydot.Dot(graph_type="digraph")
        # visited set for dfs to keep track of visited nodes
        visited = set()
        # call dfs to get the nodes in post order
        BDD.dfs(self.graph, self, visited)
        return Image(self.graph.create_png())


class BDD:
    """class for BDD"""

    def __init__(self, exp: boolfunc.Expression, ordering: list, min_optimize_idx: int=0) -> None:
        """ constructor for BDD class """
        # store the number of variables
        self.exp = exp
        # store the ordering of the variables
        self.ordering = ordering
        # node/bdd cache
        self.NODES = weakref.WeakValueDictionary()
        # get the node for zero and one
        self.BDDNODEZERO = BDDNode.getNodeZero(exp.numVars)
        self.NODES[self.BDDNODEZERO.getKey()] = self.BDDNODEZERO
        self.BDDNODEONE = BDDNode.getNodeOne(exp.numVars)
        self.NODES[self.BDDNODEONE.getKey()] = self.BDDNODEONE
        self.graph = None
        # build the bdd
        self.node = self.buildBDD(min_optimize_idx=min_optimize_idx)

    def displayGraph(self):
        """ displays the graph """
        img = self.getPng()
        display(img)
    
    def getNodeCount(self):
        """ returns node count in the graph """
        self.graph = pydot.Dot(graph_type="digraph")
        visited = set()
        BDD.dfs(self.graph, self.node, visited)
        return len(self.graph.get_nodes())

    def getPng(self):
        """ returns the png image of the graph """
        if self.graph is None:
            self.graph = pydot.Dot(graph_type="digraph")
            # visited set for dfs to keep track of visited nodes
            visited = set()
            # call dfs to get the nodes in post order
            BDD.dfs(self.graph, self.node, visited)
        return Image(self.graph.create_png())

    def getExpression(self):
        """ returns the expression of the bdd """
        vis = set()
        cubes = getExpression(self.node, vis)
        return boolfunc.Expression(cubes=cubes, numVars=self.exp.numVars)

    @staticmethod
    def dfs(graph, node, visited):
        """Iterate through nodes in DFS post-order."""
        if node.lo is not None:
            BDD.dfs(graph, node.lo, visited)
        if node.hi is not None:
            BDD.dfs(graph, node.hi, visited)
        if node not in visited:
            visited.add(node)
            if node.var == -1:
                graph.add_node(pydot.Node(node._getUid(),
                                          label=node.getLabel(),
                                          style="filled", fillcolor="orange", shape='box'))
            elif node.var == -2:
                graph.add_node(pydot.Node(node._getUid(),
                                          label=node.getLabel(),
                                          style="filled", fillcolor="lightblue", shape='box'))
            else:
                graph.add_node(pydot.Node(node._getUid(),
                                          label=node.getLabel(),
                                          style="filled", fillcolor="white"))
            if node.lo is not None:
                eLo = pydot.Edge(
                    node._getUid(), node.lo._getUid(), color='red', style='dotted')
                graph.add_edge(eLo)
            if node.hi is not None:
                eHi = pydot.Edge(
                    node._getUid(), node.hi._getUid(), color='blue')
                graph.add_edge(eHi)

    def buildBDD(self, min_optimize_idx: int=0):
        """ builds the bdd """
        return buildBDD(self.exp, self.ordering, self.NODES, idx=0, min_optimize_idx=min_optimize_idx)

    def dfsPreorder(self):
        """ returns the dfs preorder traversal of the bdd """
        visited = set()
        return _dfsPre(self.node, visited)

    def dfsPostorder(self):
        """ returns the dfs postorder traversal of the bdd """
        visited = set()
        return _dfsPost(self.node, visited)

    def bfs(self):
        """ returns the bfs traversal of the bdd """
        visited = set()
        return _bfs(self.node, visited)


def buildBDD(exp, ordering, cache, idx=0, min_optimize_idx=0):
    """ builds the bdd """
    print(f"buildBDD: idx={idx}, {ordering[idx:]}, len(ord)={len(ordering)}")
    # print(f"exp={exp}")

    # if expression is false return the zero node
    if exp.isFalse():
        if min_optimize_idx <= len(ordering):
            return cache[BDDNode.BDDNODEZEROKEY]
        if idx == len(ordering):
            return BDDNode(exp, -1)
        
    # if expression is true return the one node
    if exp.isTrue():
        if min_optimize_idx <= len(ordering):
            return cache[BDDNode.BDDNODEONEKEY]
        if idx == len(ordering):
            return BDDNode(exp, -2)
    
    # get the variable with the highest priority
    for idx2, var in enumerate(ordering[idx:]):
        # build the node for the variable
        return bddNode(exp, ordering, cache, idx + idx2, min_optimize_idx)
    
    # if no variable is present throw an error
    raise ValueError("invalid ordering list")


def bddNode(exp, ordering, cache, idx, min_optimize_idx=0):
    """ returns the bdd node """
    # print(f"bddNode: {idx}")

    # get the variable
    var = ordering[idx]
    # build the lo node
    nodeLo = buildBDD(exp.negativeCofactor(var), ordering, cache, idx + 1, min_optimize_idx)
    # build the hi node
    nodeHi = buildBDD(exp.positiveCofactor(var), ordering, cache, idx + 1, min_optimize_idx)
    key = (var, id(nodeLo), id(nodeHi))
    
    if idx >= min_optimize_idx:
        # print(f"optimize {var}:  >= {min_optimize_idx}")
        # Reduction rule 1
        # is lo is hi then return lo
        if nodeLo is nodeHi:
            exp = nodeLo.exp
            node = nodeLo
            return node
        else:
            # Reduction rule 2
            # if the node is already present in the cache then return the node
            try:
                node = cache[key]
                return node
            except KeyError:
                pass
    # else:
    #     print(f"don't optimize {var}")
    
    node = BDDNode(exp, var)
    node.lo = nodeLo
    node.hi = nodeHi
    if idx >= min_optimize_idx:
        cache[key] = node
    return node


def applyAnd(f, g, ordering, cache, idx=0):
    return BDD(f.exp.andExp(g.exp.cubes), ordering)

    if f.exp.isFalse() or g.exp.isFalse():
        return cache[BDDNode.BDDNODEZEROKEY]
    if f.exp.isTrue() and g.exp.isTrue():
        return cache[BDDNode.BDDNODEONEKEY]
    
    topvar = -1
    for idx2, var in enumerate(ordering[idx:]):
        # print(f"{var}:  {f.exp.isPresent(var)}  {g.exp.isPresent(var)}")
        if f.exp.isPresent(var) or g.exp.isPresent(var):
            topvar = var
    
    if topvar == -1:
        raise ValueError("invalid ordering")
    
    if f.var != g.var:
        raise ValueError("diff vars: ", f.var, g.var)

    f_lo = f.lo #buildBDD(f.exp.negativeCofactor(topvar), ordering, cache, idx + 1)
    f_hi = f.hi #buildBDD(f.exp.positiveCofactor(topvar), ordering, cache, idx + 1)
    g_lo = g.lo #buildBDD(g.exp.negativeCofactor(topvar), ordering, cache, idx + 1)
    g_hi = g.hi #buildBDD(g.exp.positiveCofactor(topvar), ordering, cache, idx + 1)

    nodeLo = applyAnd(f_lo, g_lo, ordering, cache, idx + 1)
    nodeHi = applyAnd(f_hi, g_hi, ordering, cache, idx + 1)

    if (nodeLo is nodeHi):
        return nodeLo

    node = BDDNode(boolfunc.Expression(), topvar)
    node.lo = nodeLo
    node.hi = nodeHi
    key = (topvar, id(nodeLo), id(nodeHi))
    cache[key] = node
    return node


def getExpression(node: BDDNode, vis: set):
    if node.getKey() == BDDNode.BDDNODEZEROKEY:
        return ()
    if node.getKey() == BDDNode.BDDNODEONEKEY:
        return ((),)
    vis.add(node)
    cubes = list()
    if node.lo and node.lo not in vis:
        loList = getExpression(node.lo, vis)
        for cube in loList:
            cubes.insert(0, (-node.var, *cube))
    if node.hi and node.hi not in vis:
        hiList = getExpression(node.hi, vis)
        for cube in hiList:
            cubes.insert(0, (node.var, *cube))
    return tuple(set(cubes))


def _dfsPre(node, visited):
    """Iterate through nodes in DFS pre-order."""
    if node not in visited:
        visited.add(node)
        yield node
    if node.lo is not None:
        yield from _dfsPre(node.lo, visited)
    if node.hi is not None:
        yield from _dfsPre(node.hi, visited)


def _dfsPost(node, visited):
    """Iterate through nodes in DFS post-order."""
    if node.lo is not None:
        yield from _dfsPost(node.lo, visited)
    if node.hi is not None:
        yield from _dfsPost(node.hi, visited)
    if node not in visited:
        visited.add(node)
        yield node


def _bfs(node, visited):
    """Iterate through nodes in BFS order."""
    queue = collections.deque()
    queue.appendleft(node)
    while queue:
        node = queue.pop()
        if node not in visited:
            if node.lo is not None:
                queue.appendleft(node.lo)
            if node.hi is not None:
                queue.appendleft(node.hi)
            visited.add(node)
            yield node
