/**
  MIT License

  Copyright (c) 2020 John Jackson

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
 */
/*******************************************************************************
 * Weighted maximum matching in general graphs.
 ******************************************************************************/
/**
  This code is based on a Python implementation by Joris van Rantwijk, who had
  consulted a C implementation by Ed Rothberg.

  Joris's comment from the Python version:

  > The algorithm is taken from "Efficient Algorithms for Finding Maximum
  > Matching in Graphs" by Zvi Galil, ACM Computing Surveys, 1986. It is based
  > on the "blossom" method for finding augmenting paths and the "primal-dual"
  > method for finding a matching of maximum weight, both due to Jack Edmonds.
  > Some ideas came from the "Implementation of algorithms for maximum matching
  > in non-bipartite graphs" by H.J. Gabow, Standford Ph.D. thesis, 1973.
  >
  > Many terms used in the comments (sub-blossom, T-vertex) come from the paper
  > by Galil; read the paper before reading this code.

  Thanks to Reason's strong typing and some clever ADTs, this version of the
  algorithm is almost entirely safe. Yet, there remain a few exceptional
  situations that are difficult to represent on a type level.

  Safe labeling is unsolved. Labels must conform to a pattern (T->S) but the
  current types do not enforce it. This problem is complicated by the fact that
  each vertex's label is usually determined by its top-level parent blossom's
  label, not its own. The dynamic nature of these variables makes it a challenge
  to enforce labels in an efficient way.

  Performance isn't everything, but regressions should be avoided.

  This code uses features from the BuckleScript compiler to output performant
  JavaScript. It will require modification to compile on other platforms.
 */
/*******************************************************************************
 * Part I: The types
 ******************************************************************************/
module ParityList = {
  /**
   * This works like a linked list, only with the parity enforced.
   * It's used to store each blossom's children. Whether a child is odd or even
   * is significant.
   */
  type even('a) =
    | Empty
    | Even('a, odd('a))
  and odd('a) =
    | Odd('a, even('a));

  module Infix = {
    /**
     * Append an item to an odd list.
     * (Has an odd number of dots = appends to an odd list.)
     */
    let (<.>) = (l, x) => Even(x, l);

    /**
     * Append an item to an even list.
     * (Has an even number of dots = appends to an even list.)
     */
    let (<:>) = (l, x) => Odd(x, l);
  };

  module Even = {
    open Infix;
    type t('a) = even('a);

    let rec reduceU = (l, ~init, ~f) =>
      switch (l) {
      | Empty => init
      | Even(a, Odd(b, tail)) =>
        reduceU(tail, ~init=f(. f(. init, a), b), ~f)
      };

    let reverse = l => {
      let rec loop = (acc, l) =>
        switch (l) {
        | Empty => acc
        | Even(a, Odd(b, tail)) => loop(acc <:> a <.> b, tail)
        };
      loop(Empty, l);
    };

    let concat = (l1, l2) => {
      let rec loop = (acc, l1, l2) =>
        switch (l1, l2) {
        | (Empty, Empty) => reverse(acc)
        | (Empty, Even(x, Odd(y, tail))) =>
          loop(Even(y, Odd(x, acc)), Empty, tail)
        | (Even(x, Odd(y, tail)), l) =>
          loop(Even(y, Odd(x, acc)), tail, l)
        };
      loop(Empty, l1, l2);
    };
  };

  module Odd = {
    open Infix;
    type t('a) = odd('a);

    let make = x => Odd(x, Empty);

    let rec reduceU = (l, ~init, ~f) =>
      switch (l) {
      | Odd(a, Empty) => f(. init, a)
      | Odd(a, Even(b, tail)) =>
        reduceU(tail, ~init=f(. f(. init, a), b), ~f)
      };

    let reverse = (Odd(head, tail)) => {
      let rec loop = (acc, l) =>
        switch (l) {
        | Empty => acc
        | Even(a, Odd(b, tail)) => loop(acc <.> a <:> b, tail)
        };
      loop(make(head), tail);
    };

    let forEachU = (l, ~f) => reduceU(l, ~init=(), ~f=(. _, x) => f(. x));

    let concat = (l1, l2) => {
      let rec loop = (acc, l) =>
        switch (l) {
        | Odd(a, Empty) => acc <.> a |> Even.reverse
        | Odd(a, Even(b, tail)) => loop(acc <.> a <:> b, tail)
        };
      loop(reverse(l1), l2);
    };

    let concatEven = (Odd(head, tail), l2) =>
      Odd(head, Even.concat(tail, l2));

    let trimToU = (Odd(head, tail), ~f) => {
      let rec loop = (acc, l) =>
        switch (l) {
        | Even(a, _) when f(. a) => Some(reverse(acc))
        | Empty => None
        | Even(a, Odd(b, l)) => loop(Odd(b, Even(a, acc)), l)
        };
      loop(make(head), tail);
    };
  };
};

type stage =
  | Endstage
  | NotEndstage;

type cardinality = [ | `Max | `NotMax];

type allowable =
  | Allowed
  | NotAllowed;

type graph('v) = {
  vertices: list(vertex('v)),
  mutable blossoms: list(blossom('v)),
  maxWeight: float,
  edges: list(edge('v)),
  vertexSize: int /* A cached size of the vertices list. */
}
/**
 * Edges represent a weighted connection between two vertices.
 */
and edge('v) = {
  i: vertex('v), /* Not modified by the algorithm. */
  j: vertex('v), /* Not modified by the algorithm. */
  weight: float, /* Not modified by the algorithm. */
  /* If Allowed, the edge has zero slack in the optimization problem. If
     NotAllowed, the edge's slack may or may not be zero. */
  mutable allowable,
}
/**
 * An endpoint represents where an edge connects to a vertex;
 * E.g.: `I(edge)` represents the vertex at `edge.i`.
 */
and endpoint('v) =
  | I(edge('v))
  | J(edge('v))
and basicNode('v, 'content, 'fields) = {
  /* For a vertex, this is the data received from the input. It can be any type.
     For a blossom, it is an `int`. */
  content: 'content,
  /* The node's immediate parent (sub-)blossom, or `None` if the vertex is a
     top-level blossom. */
  mutable parent: option(blossom('v)),
  /* The node's variable in the dual optimization problem. */
  mutable dualVar: float,
  /* If the node is free (or unreached inside a T-blossom), its best edge is
     the edge to an S-vertex with least slack, or `None` if there is no such
     edge.
     If it is a (possibly trivial) top-level S-blossom, its best edge is the
     least-slack edge to a different S-blossom, or `None` if there is no
     such edge.
     This is used for efficient computation of delta2 and delta3. */
  mutable bestEdge: option(edge('v)),
  /* The label of the node is found by looking at the label of its top-level
     containing blossom. If the node is inside a T-blossom, its label is T if it
     is reachable from an S-vertex outside the blossom.
     Labels are assigned during a stage and reset after each augmentation. */
  mutable label: label('v),
  fields: 'fields,
}
/**
 * Vertices represent nodes of the input graph.
 */
and vertexFields('v) = {
  /* A list of remote endpoints of the edges attached to the vertex. */
  /* Not modified by the algorithm. */
  mutable neighbors: list(endpoint('v)),
  /* The top-level blossom to which the vertex belongs. If the
     vertex is a top-level blossom, then inBlossom will point to itself.
     Initially, all vertices are top-level blossoms, and their own
     inBlossoms. */
  mutable inBlossom: anyNode('v),
}
and vertex('v) = basicNode('v, 'v, vertexFields('v))
/**
 * Blossoms, also called "super-vertices," are nodes that contain vertices and
 * other blossoms.
 */
and blossomFields('v) = {
  /* The blossom's base vertex and the head of its list of children. */
  mutable base: vertex('v),
  /* A list of the blossom's sub-blossoms, starting with the base and going
     around the blossom. */
  mutable children: ParityList.Odd.t(child('v)),
  /* A list of least-slack edges to neighboring S-blossoms. This is used for
     efficient computation of delta3. */
  /* We're using an association list to map nodes to edges. There are
     probably more performant structures we could use, like maps, but this
     is uncomplicated and works. */
  mutable blossomBestEdges: list((anyNode('v), edge('v))),
}
and blossom('v) = basicNode('v, int, blossomFields('v))
and child('v) = {
  node: anyNode('v),
  /* The endpoint that connects the child to the next child in the list. */
  endpoint: endpoint('v),
}
and anyNode('v) =
  | Vertex(vertex('v))
  | Blossom(blossom('v))
/**
 * Top-level blossoms are either unlabeled ("free"), labeled S with no
 * endpoint, S with an endpoint, or T with an endpoint.
 *
 * The label endpoint for a top-level blossom is the remote endpoint of the
 * edge through which the blossom obtained its label.
 *
 * If a vertex is inside a T blossom and is also labeled T, then the endpoint
 * is the remote endpoint of the edge through which the vertex is reachable
 * from outside the blossom.
 */
and label('v) =
  | Free
  | SingleS /* Only assigned when a stage begins. */
  | S(endpoint('v))
  | T(endpoint('v));

/*******************************************************************************
 * Part II: Accessor and utility functions
 ******************************************************************************/

module Edge = {
  type t('v) = edge('v);

  /**
   * Return the slack of the given edge. Does not work inside blossoms.
   */
  let slack = k => k.i.dualVar +. k.j.dualVar -. k.weight;

  let _debug = k => {
    let i = k.i.content;
    let j = k.j.content;
    let w = k.weight;
    {j|{i: $i, j: $j, weight: $w}|j};
  };
};

module Endpoint = {
  type t('v) = endpoint('v);

  let toEdge = (J(edge) | I(edge)) => edge;

  let toVertex =
    fun
    | I(edge) => edge.i
    | J(edge) => edge.j;

  let reverse =
    fun
    | I(edge) => J(edge)
    | J(edge) => I(edge);

  /**
   * This is equivalent to, but more performant than, `reverse |> toVertex`.
   */
  let toReverseVertex =
    fun
    | I(edge) => edge.j
    | J(edge) => edge.i;

  let _debug =
    fun
    | I(edge) => "I(" ++ Edge._debug(edge) ++ ")"
    | J(edge) => "J(" ++ Edge._debug(edge) ++ ")";
};

module Vertex = {
  type t('v) = vertex('v);

  /* We can use reference equality (===) even though we don't know the vertex
     types because they never change after the graph is created. */
  let eq: (t('v), t('v)) => bool = (a, b) => a.content === b.content;

  let _debug: t('v) => string = v => Js.String.make(v.content);
};

module Blossom = {
  type t('v) = blossom('v);

  let eq: (t('v), t('v)) => bool = (a, b) => a.content == b.content;

  let _debug: t('v) => string = b => Js.String.make(b.content);
};

module Node = {
  type t('v) = anyNode('v);

  let base =
    fun
    | Vertex(vertex) => vertex
    | Blossom(blossom) => blossom.fields.base;

  let eq = (a, b) =>
    switch (a, b) {
    | (Vertex(a), Vertex(b)) => Vertex.eq(a, b)
    | (Blossom(a), Blossom(b)) => Blossom.eq(a, b)
    | (Vertex(_), Blossom(_))
    | (Blossom(_), Vertex(_)) => false
    };

  let eqB = (a, b) =>
    switch (a) {
    | Blossom(a) => Blossom.eq(a, b)
    | Vertex(_) => false
    };

  let setParent = (node, ~b) =>
    switch (node) {
    | Vertex(vertex) => vertex.parent = Some(b)
    | Blossom(blossom) => blossom.parent = Some(b)
    };

  let bestEdge =
    fun
    | Vertex({bestEdge, _})
    | Blossom({bestEdge, _}) => bestEdge;

  let setBestEdge = (node, ~edge) =>
    switch (node) {
    | Vertex(v) => v.bestEdge = Some(edge)
    | Blossom(b) => b.bestEdge = Some(edge)
    };

  let removeBestEdge =
    fun
    | Vertex(v) => v.bestEdge = None
    | Blossom(b) => b.bestEdge = None;

  let label =
    fun
    | Vertex({label, _})
    | Blossom({label, _}) => label;

  let _debug =
    fun
    | Vertex({content, _}) => {j|Vertex($content)|j}
    | Blossom({content, _}) => {j|Blossom($content)|j};

  module Infix = {
    let (=|=) = eq;
  };

  module Leaves = {
    /**
     * Reduce over the leaves of a node. Leaves are the vertices in a blossom's
     * children, as well as the vertices in any of its sub-blossom's children.
     */
    let rec reduceU = (b, ~init, ~f) =>
      switch (b) {
      | Vertex(vertex) => f(. init, vertex)
      | Blossom({fields: {children, _}, _}) =>
        ParityList.Odd.reduceU(children, ~init, ~f=(. init, child) =>
          reduceU(child.node, ~init, ~f)
        )
      };

    let toList = (~init=[], b) =>
      reduceU(b, ~init, ~f=(. leaves, v) => [v, ...leaves]);

    let forEachU = (b, ~f) => reduceU(b, ~init=(), ~f=(. _, v) => f(. v));

    let _debug = b =>
      b->toList->Belt.List.map(Vertex._debug)->Belt.List.toArray;
  };
};

module Child = {
  type t('v) = child('v);

  let _debug = c =>
    ParityList.Odd.reduceU(c, ~init=[||], ~f=(. acc, {node, endpoint}) =>
      Belt.Array.concat(
        acc,
        [|(Node._debug(node), Endpoint._debug(endpoint))|],
      )
    );
};

module Mates = {
  /* Maps vertices to remote endpoints of their attached edges. */
  type t('v, 'id) = Belt.Map.t('v, Endpoint.t('v), 'id);

  module Internal = {
    let make = Belt.Map.make;

    let get = (mates, v) => Belt.Map.get(mates, v.content);

    let setEdge = (mates, edge) =>
      mates
      ->Belt.Map.set(edge.i.content, J(edge))
      ->Belt.Map.set(edge.j.content, I(edge));

    let set = (mates, v, p) => Belt.Map.set(mates, v.content, p);

    let has = (mates, v) => Belt.Map.has(mates, v.content);
  };

  let exportEndpoint = p => Endpoint.toVertex(p).content;

  /* Public functions */

  let get = (mates, v) =>
    switch (Belt.Map.get(mates, v)) {
    | None => None
    | Some(p) => Some(exportEndpoint(p))
    };

  let reduceU = (mates, ~init, ~f) =>
    Belt.Map.reduceU(mates, init, (. acc, v1, p) =>
      f(. acc, v1, exportEndpoint(p))
    );

  let reduce = (mates, ~init, ~f) =>
    reduceU(mates, ~init, ~f=(. acc, v1, v2) => f(acc, v1, v2));

  let forEachU = (mates, ~f) =>
    Belt.Map.forEachU(mates, (. v1, p) => f(. v1, exportEndpoint(p)));

  let forEach = (mates, ~f) => forEachU(mates, ~f=(. v1, v2) => f(v1, v2));

  let toList = reduce(~init=[], ~f=(acc, v1, v2) => [(v1, v2), ...acc]);

  let toMap = mates =>
    Belt.(
      Map.reduceU(
        mates, Map.make(~id=Map.getId(mates)), (. acc, vertex, mate) =>
        Map.set(acc, vertex, exportEndpoint(mate))
      )
    );

  let isEmpty = Belt.Map.isEmpty;

  let has = Belt.Map.has;

  let _debug = mates => mates |> toList |> Belt.List.toArray;
};

module Label = {
  let _debug =
    fun
    | Free => "Free"
    | SingleS => "SingleS"
    | S(endpoint) => "S(" ++ Endpoint._debug(endpoint) ++ ")"
    | T(endpoint) => "T(" ++ Endpoint._debug(endpoint) ++ ")";

  /**
   * Label a vertex S and add its inBlossom's children to the queue.
   */
  let assignS = (~v, ~label, ~queue) => {
    let b = v.fields.inBlossom;
    [%log.debug
      "assignLabel";
      ("Vertex", Vertex._debug(v));
      ("Blossom", Node._debug(b));
      ("Label", _debug(label));
      ("PUSH", Node.Leaves._debug(b))
    ];
    switch (b) {
    | Blossom(b) =>
      b.label = label;
      b.bestEdge = None;
    | Vertex(_) => v.bestEdge = None
    };
    v.bestEdge = None;
    v.label = label;
    Node.Leaves.toList(b, ~init=queue);
  };

  /**
   * Label a vertex T, label its mate S, and add its mate's inBlossom's children
   * to the queue.
   */
  let assignT = (~v, ~p, ~mates) => {
    let b = v.fields.inBlossom;
    [%log.debug
      "assignLabel";
      ("Vertex", Vertex._debug(v));
      ("Blossom", Node._debug(b));
      ("Label", _debug(T(p)))
    ];
    let label = T(p);
    switch (b) {
    | Blossom(b) =>
      b.label = label;
      b.bestEdge = None;
    | Vertex(_) => v.bestEdge = None
    };
    v.bestEdge = None;
    v.label = label;
    switch (Mates.Internal.get(mates, Node.base(b))) {
    | None => failwith("Needed mate.")
    | Some(matep) =>
      let mate = Endpoint.toVertex(matep);
      assignS(~v=mate, ~label=S(Endpoint.reverse(matep)));
    };
  };

  /**
   * Label a vertex T without stepping through to its mate.
   */
  let assignTSingleVertex = (~v, ~p) => v.label = T(p);

  /**
   * Label a vertex or blossom T without stepping through to its mate.
   */
  let assignTSingle = (~w, ~p) =>
    switch (w) {
    | Vertex(v) => assignTSingleVertex(~v, ~p)
    | Blossom(b) => b.label = T(p)
    };
};

/*******************************************************************************
 * Part III: Let's start making a graph
 ******************************************************************************/

module Graph = {
  /**
   * Turn the raw input into a recursive graph.
   * Compared to similar algorithms, this is the most computationally expensive
   * part of this implementation.
   */
  let makeGraph = (type v, rawEdges, ~id: Belt.Id.comparable(v, 'id), ~cmp) => {
    /* We need to be able to validate the input and identify duplicate vertices
       and edges. This set and map will help us do it efficiently. */
    let cmpU = (. a, b) => cmp(a, b);
    /* Create a set of tuples to store the pairs of vertices in each edge. */
    module EdgeCmp =
      Belt.Id.MakeComparableU({
        type t = (v, v);
        /* This only works if the vertices are always in the same order.
           See `edge'` below. */
        let cmp =
          (. (a, b), (y, z)) =>
            switch (cmpU(. a, y), cmpU(. b, z)) {
            | (0, 0) => 0
            | (c, d) =>
              switch (c + d) {
              | 0 => c
              | e => e
              }
            };
      });
    let edgeSet = Belt.Set.make(~id=(module EdgeCmp));
    let vertexMap = Belt.Map.make(~id);

    let rec loop =
            (
              ~rawEdges,
              ~edges,
              ~edgeSet,
              ~vertices,
              ~vertexMap,
              ~vertexSize,
              ~maxWeight,
            ) =>
      switch (rawEdges) {
      | [] =>
        Belt.List.forEachU(vertices, (. v) => v.dualVar = maxWeight);
        {vertices, blossoms: [], maxWeight, edges, vertexSize};
      | [(iId, jId, weight), ...rawEdges] =>
        let edgeComparison = cmpU(. iId, jId);
        /* To avoid duplicates, this ensures they're always ordered the same. */
        let edge' =
          switch (edgeComparison) {
          | 1 => (iId, jId)
          | _ => (jId, iId)
          };
        if (edgeComparison == 0 || Belt.Set.has(edgeSet, edge')) {
          loop(
            ~rawEdges,
            ~edges,
            ~edgeSet,
            ~vertices,
            ~vertexMap,
            ~vertexSize,
            ~maxWeight,
          );
        } else {
          let maxWeight = max(maxWeight, weight);
          let edgeSet = Belt.Set.add(edgeSet, edge');
          /* See if `i` or `j` are already created. If they are, update them. */
          switch (Belt.Map.(get(vertexMap, iId), get(vertexMap, jId))) {
          | (Some(i), Some(j)) =>
            let edge = {i, j, weight, allowable: NotAllowed};
            i.fields.neighbors = [J(edge), ...i.fields.neighbors];
            j.fields.neighbors = [I(edge), ...j.fields.neighbors];
            loop(
              ~rawEdges,
              ~edges=[edge, ...edges],
              ~edgeSet,
              ~vertices,
              ~vertexMap,
              ~vertexSize,
              ~maxWeight,
            );
          | (Some(i), None) =>
            let rec edge = {i, j, weight, allowable: NotAllowed}
            and j = {
              content: jId,
              parent: None,
              dualVar: 0.,
              bestEdge: None,
              label: Free,
              fields: {
                neighbors: [I(edge)],
                inBlossom: Vertex(j),
              },
            };
            i.fields.neighbors = [J(edge), ...i.fields.neighbors];
            loop(
              ~rawEdges,
              ~edges=[edge, ...edges],
              ~edgeSet,
              ~vertices=[j, ...vertices],
              ~vertexMap=Belt.Map.set(vertexMap, jId, j),
              ~vertexSize=succ(vertexSize),
              ~maxWeight,
            );
          | (None, Some(j)) =>
            let rec edge = {i, j, weight, allowable: NotAllowed}
            and i = {
              content: iId,
              parent: None,
              dualVar: 0.,
              bestEdge: None,
              label: Free,
              fields: {
                neighbors: [J(edge)],
                inBlossom: Vertex(i),
              },
            };
            j.fields.neighbors = [I(edge), ...j.fields.neighbors];
            loop(
              ~rawEdges,
              ~edges=[edge, ...edges],
              ~edgeSet,
              ~vertices=[i, ...vertices],
              ~vertexMap=Belt.Map.set(vertexMap, iId, i),
              ~vertexSize=succ(vertexSize),
              ~maxWeight,
            );
          | (None, None) =>
            let rec edge = {i, j, weight, allowable: NotAllowed}
            and i = {
              content: iId,
              parent: None,
              dualVar: 0.,
              bestEdge: None,
              label: Free,
              fields: {
                neighbors: [J(edge)],
                inBlossom: Vertex(i),
              },
            }
            and j = {
              content: jId,
              parent: None,
              dualVar: 0.,
              bestEdge: None,
              label: Free,
              fields: {
                neighbors: [I(edge)],
                inBlossom: Vertex(j),
              },
            };
            loop(
              ~rawEdges,
              ~edges=[edge, ...edges],
              ~edgeSet,
              ~vertices=[i, j, ...vertices],
              ~vertexMap=
                vertexMap->Belt.Map.set(iId, i)->Belt.Map.set(jId, j),
              ~vertexSize=vertexSize |> succ |> succ,
              ~maxWeight,
            );
          };
        };
      };
    loop(
      ~rawEdges,
      ~vertices=[],
      ~edges=[],
      ~edgeSet,
      ~vertexMap,
      ~vertexSize=0,
      ~maxWeight=0.,
    );
  };
  /* Aliasing `make` and `makeGraph` for better JavaScript debugging. */
  let make = makeGraph;

  let updateDualVarsByDelta = (graph, ~delta) => {
    Belt.List.forEachU(graph.vertices, (. v) =>
      v.dualVar = {
        switch (Node.label(v.fields.inBlossom)) {
        /* S-vertex: u = u - delta */
        | SingleS
        | S(_) => v.dualVar -. delta
        /* T-vertex: u = u + delta */
        | T(_) => v.dualVar +. delta
        | Free => v.dualVar
        };
      }
    );
    Belt.List.forEachU(graph.blossoms, (. b) =>
      switch (b) {
      | {parent: None, label: SingleS | S(_), _} =>
        /* top-level S-blossom: z = z + delta */
        b.dualVar = b.dualVar +. delta
      | {parent: None, label: T(_), _} =>
        /* top-level T-blossom: z = z - delta */
        b.dualVar = b.dualVar -. delta
      | {parent: Some(_), _}
      | {label: Free, _} => ()
      }
    );
  };
};

/*******************************************************************************
 * Part IV: Add, augment, and expand blossoms
 ******************************************************************************/

module AddBlossom = {
  /* First, we trace the graph to see if we are able to add a blossom. */

  type traceResult('v, 'a) =
    | DeadEnd(Node.t('v), 'a)
    | FoundChild(Node.t('v), 'a);

  type scanResult('v) =
    | AugmentingPath
    | NewBlossom(ParityList.Odd.t(Child.t('v)));

  /**
   * Trace back to the next S-blossom and add the path of blossoms to the list
   * of children.
   */
  let traceBackward = (w, backChildren) =>
    switch (Node.label(w)) {
    | Free
    | SingleS => DeadEnd(w, backChildren)
    | T(_) => failwith("Label should only be S.")
    | S(p) =>
      let w' = Endpoint.toVertex(p).fields.inBlossom;
      switch (Node.label(w')) {
      | Free
      | SingleS
      | S(_) => failwith("Label should only be T.")
      | T(p') =>
        let backChildren =
          ParityList.Infix.(
            backChildren
            <:> {node: w, endpoint: Endpoint.reverse(p)}
            <.> {node: w', endpoint: Endpoint.reverse(p')}
          );
        let nextW = Endpoint.toVertex(p').fields.inBlossom;
        FoundChild(nextW, backChildren);
      };
    };

  /**
   * Trace forward to the next S-blossom and add the path of blossoms to the
   * list of children.
   */
  let traceForward = (v, frontChildren) =>
    switch (Node.label(v)) {
    | Free
    | SingleS => DeadEnd(v, frontChildren)
    | T(_) => failwith("Label should only be S.")
    | S(p) =>
      let v' = Endpoint.toVertex(p).fields.inBlossom;
      switch (Node.label(v')) {
      | Free
      | SingleS
      | S(_) => failwith("Label should only be T.")
      | T(p') =>
        let lastV = Endpoint.toVertex(p').fields.inBlossom;
        let frontChildren =
          ParityList.Infix.(
            frontChildren
            <.> {node: v', endpoint: p}
            <:> {node: lastV, endpoint: p'}
          );
        FoundChild(lastV, frontChildren);
      };
    };

  /**
   * Scan the found children to see if there's a connecting "base" node.
   */
  let findConnection = (lastV, nextW, front, back) => {
    open ParityList;
    let children = Odd.concatEven(front, Even.reverse(back));
    if (Node.eq(lastV, nextW)) {
      Some(children);
    } else {
      Odd.trimToU(children, ~f=(. {node, _}) => Node.eq(node, lastV));
    };
  };

  /**
   * Trace back from the given edge's vertices to discover either a new blossom
   * or an augmenting path.
   */
  let scanForBlossom = edge => {
    [%log.debug
      "scanBlossom";
      ("v", Vertex._debug(edge.i));
      ("w", Vertex._debug(edge.j))
    ];
    open ParityList;
    let rec loop = (frontPath, backPath) =>
      switch (frontPath, backPath) {
      | (DeadEnd(lastV, front), DeadEnd(nextW, back)) =>
        switch (findConnection(lastV, nextW, front, back)) {
        | Some(children) => NewBlossom(children)
        | None => AugmentingPath
        }
      | (DeadEnd(lastV, front) as frontPath, FoundChild(nextW, back)) =>
        switch (findConnection(lastV, nextW, front, back)) {
        /* The first front child was a SingleS; the back traced around to it. */
        | Some(children) => NewBlossom(children)
        | None => loop(frontPath, traceBackward(nextW, back))
        }
      | (FoundChild(lastV, front), DeadEnd(nextW, back) as backPath) =>
        switch (findConnection(lastV, nextW, front, back)) {
        /* The first back child was a SingleS; the front traced around to it. */
        | Some(children) => NewBlossom(children)
        | None => loop(traceForward(lastV, front), backPath)
        }
      | (FoundChild(lastV, front), FoundChild(nextW, back)) =>
        switch (findConnection(lastV, nextW, front, back)) {
        | Some(children) => NewBlossom(children)
        | None =>
          switch (traceBackward(nextW, back)) {
          | FoundChild(nextW, back) as backPath =>
            switch (findConnection(lastV, nextW, front, back)) {
            | Some(children) => NewBlossom(children)
            | None => loop(traceForward(lastV, front), backPath)
            }
          | DeadEnd(_) as backPath =>
            loop(traceForward(lastV, front), backPath)
          }
        }
      };
    let initialV = edge.i.fields.inBlossom;
    loop(
      /* Manually add the i child to connect the two lists. */
      FoundChild(initialV, Odd.make({node: initialV, endpoint: I(edge)})),
      FoundChild(edge.j.fields.inBlossom, Empty),
    );
  };

  /* Now we can create a blossom. */

  let bestEdgesReducerHelper = (~b, ~neighbor as w, ~bestEdgeList, ~edge) =>
    switch (Node.eqB(w, b), Node.label(w)) {
    | (false, SingleS | S(_)) =>
      switch (Belt.List.getAssoc(bestEdgeList, w, Node.eq)) {
      | Some(neighbor) when Edge.slack(edge) < Edge.slack(neighbor) =>
        Belt.List.setAssoc(bestEdgeList, w, edge, Node.eq)
      | None => Belt.List.setAssoc(bestEdgeList, w, edge, Node.eq)
      | _ => bestEdgeList
      }
    | (true, SingleS | S(_))
    | (true | false, Free | T(_)) => bestEdgeList
    };

  let endpointReducer = b =>
    (. bestEdgeList, endpoint) =>
      bestEdgesReducerHelper(
        ~b,
        ~neighbor=Endpoint.toVertex(endpoint).fields.inBlossom,
        ~bestEdgeList,
        ~edge=Endpoint.toEdge(endpoint),
      );

  let bestEdgesReducer = b =>
    (. bestEdgeList, (_node, edge)) =>
      bestEdgesReducerHelper(
        ~b,
        ~neighbor=
          Node.eqB(edge.j.fields.inBlossom, b)
            ? edge.i.fields.inBlossom : edge.j.fields.inBlossom,
        ~bestEdgeList,
        ~edge,
      );

  let computeBestEdges = b =>
    ParityList.Odd.reduceU(
      b.fields.children,
      ~init=[],
      ~f=(. bestEdgeList, child) => {
        let bestEdgeList =
          switch (child.node) {
          /* This sub-blossom does not have a list of least-slack edges; get
             the information from the vertices. */
          | Blossom({fields: {blossomBestEdges: [], _}, _}) as node
          | Vertex(_) as node =>
            Node.Leaves.reduceU(
              node, ~init=bestEdgeList, ~f=(. bestEdgeList, v) =>
              Belt.List.reduceU(
                v.fields.neighbors,
                bestEdgeList,
                endpointReducer(b),
              )
            )
          /* Walk this sub-blossom's least-slack edges. */
          | Blossom({fields: {blossomBestEdges, _}, _}) =>
            Belt.List.reduceU(
              blossomBestEdges,
              bestEdgeList,
              bestEdgesReducer(b),
            )
          };
        /* Forget about least-slack edges of this sub-blossom. */
        switch (child.node) {
        | Vertex(v) => v.bestEdge = None
        | Blossom(b) =>
          b.bestEdge = None;
          b.fields.blossomBestEdges = [];
        };
        bestEdgeList;
      },
    );

  /**
   * Construct a new blossom with a given base, containing an edge which
   * connects a pair of S vertices. Label the new blossom as S; relabel its
   * T-vertices to S and add them to the queue.
   */
  let makeBlossom = (graph, children, queue) => {
    let content =
      switch (graph.blossoms) {
      | [] => 0
      | [{content, _}, ..._] => succ(content)
      };
    let ParityList.Odd({node: baseNode, _}, _) = children;
    let b = {
      content,
      parent: None,
      dualVar: 0.,
      bestEdge: None,
      label: Node.label(baseNode),
      fields: {
        base: Node.base(baseNode),
        children,
        blossomBestEdges: [],
      },
    };
    ParityList.Odd.forEachU(children, ~f=(. c) =>
      Node.setParent(c.node, ~b)
    );
    /* Relabel the vertices. */
    let queue =
      Node.Leaves.reduceU(
        Blossom(b),
        ~init=queue,
        ~f=(. queue, v) => {
          let oldLabel = Node.label(v.fields.inBlossom);
          v.fields.inBlossom = Blossom(b);
          switch (oldLabel) {
          /* This T-Vertex now turns into an S-vertex because it becomes part
             of an S-blossom; add it to the queue. */
          | T(_) => [v, ...queue]
          | Free
          | SingleS
          | S(_) => queue
          };
        },
      );
    graph.blossoms = [b, ...graph.blossoms];
    /* Compute the blossom's best edges. */
    let bestEdges = computeBestEdges(b);
    let bestEdge =
      Belt.List.reduceU(bestEdges, b.bestEdge, (. bestEdge, (_node, edge)) =>
        switch (bestEdge) {
        | None => Some(edge)
        | Some(newBestEdge) when Edge.(slack(edge) < slack(newBestEdge)) =>
          Some(edge)
        | _ => bestEdge
        }
      );
    switch (bestEdge) {
    | Some(edge) => b.bestEdge = Some(edge)
    | None => b.bestEdge = None
    };
    b.fields.blossomBestEdges = bestEdges;
    queue;
  };
  /* Aliasing `make` and `makeBlossom` for better JavaScript debugging. */
  let make = makeBlossom;
};

module ModifyBlossom = {
  open ParityList;
  /* When augmenting or expanding a blossom, we'll need to separate the base
     child, the "entry" child, and the list of children between them. Whether
     the entry child was odd or even will determine whether we move forward or
     backward when processing the children. */
  type splitChildren('v) =
    | NoSplit({
        base: Child.t('v),
        rest: Even.t(Child.t('v)),
      })
    | GoForward({
        base: Child.t('v),
        front: Even.t(Child.t('v)),
        entry: Child.t('v),
        back: Odd.t(Child.t('v)),
      })
    | GoBackward({
        base: Child.t('v),
        front: Odd.t(Child.t('v)),
        entry: Child.t('v),
        back: Even.t(Child.t('v)),
      });

  /**
   * Remove the base child and split the remaining children into two lists, one
   * before and one and after the entry child.
   */
  let splitChildren = (children, entryChild) => {
    open Node.Infix;
    open ParityList.Infix;
    let Odd(base, rest) = children;
    let rec loop = (front, back) =>
      switch (back) {
      | Empty when base.node =|= entryChild => NoSplit({base, rest})
      | Empty => failwith("Entry child not found.")
      | Even(child, back) when child.node =|= entryChild =>
        GoForward({base, front: Even.reverse(front), entry: child, back})
      | Even(child, Odd(child', back)) when child'.node =|= entryChild =>
        GoBackward({
          base,
          front: Odd.reverse(front <:> child),
          entry: child',
          back,
        })
      | Even(child, Odd(child', back)) =>
        loop(front <:> child <.> child', back)
      };
    loop(Empty, rest);
  };

  let rec bubbleBlossomTree = (node, parent, b) =>
    switch (parent) {
    | None => failwith("There should be a parent.")
    | Some(parent) when Blossom.eq(parent, b) => node
    | Some(parent) => bubbleBlossomTree(Blossom(parent), parent.parent, b)
    };

  type direction =
    | Backward
    | Forward;

  /**
   * Swap matched/unmatched edges over an alternating path through a blossom
   * between vertex `v` and the base vertex. Keep blossom bookkeeping
   * consistent.
   */
  let rec augment = (b, v, mates) => {
    [%log.debug
      "augmentBlossom";
      ("Blossom", Blossom._debug(b));
      ("Vertex", Vertex._debug(v));
      ("Mates", Mates._debug(mates))
    ];
    /* Bubble up through the blossom tree from from the vertex to an immediate
       sub-blossom of `b`. */
    let t = bubbleBlossomTree(Vertex(v), v.parent, b);
    /* Recursively deal with the first sub-blossom. */
    let mates =
      switch (t) {
      | Blossom(b) => augment(b, v, mates)
      | Vertex(_) => mates
      };
    /* Figure out how we'll go 'round the blossom. */
    let (moveList, direction, children) =
      switch (splitChildren(b.fields.children, t)) {
      | NoSplit(_) => (Empty, Backward, b.fields.children)
      | GoForward({base, front, entry, back}) =>
        let moveList = Odd.concat(back, Odd.make(base));
        /* Rotate the list of sub-blossoms to put the new base at the front. */
        let children = Odd(entry, Odd.concat(back, Odd(base, front)));
        (moveList, Forward, children);
      | GoBackward({base, front, entry, back}) =>
        let moveList = Even.reverse(Even(base, front));
        /* Rotate the list of sub-blossoms to put the new base at the front. */
        let children = Odd(entry, Even.concat(back, Even(base, front)));
        (moveList, Backward, children);
      };
    b.fields.base = v;
    b.fields.children = children;
    let rec loopToBase = (moveList, mates) =>
      switch (moveList) {
      | Empty => mates
      /* Step into the next two sub-blossoms and augment them recursively. */
      | Even(child, Odd(child', rest)) =>
        let p =
          switch (direction) {
          | Forward => child.endpoint
          | Backward => Endpoint.reverse(child'.endpoint)
          };
        let mates =
          switch (child.node) {
          | Blossom(b) => augment(b, Endpoint.toVertex(p), mates)
          | Vertex(_) => mates
          };
        let mates =
          switch (child'.node) {
          | Blossom(b) => augment(b, Endpoint.toReverseVertex(p), mates)
          | Vertex(_) => mates
          };
        /* Match the edge connecting those sub-blossoms. */
        let mates = Mates.Internal.setEdge(mates, Endpoint.toEdge(p));
        [%log.debug
          "PAIR";
          ("v", p |> Endpoint.toVertex |> Vertex._debug);
          ("w", p |> Endpoint.toReverseVertex |> Vertex._debug)
        ];
        loopToBase(rest, mates);
      };
    loopToBase(moveList, mates);
  };

  let rec relabelToBase =
          (childsToBase, nextEndpoint, queue, mates, direction) =>
    switch (childsToBase) {
    | Odd(_, Empty) => (nextEndpoint, queue)
    | Odd({endpoint, _}, Even({endpoint: endpoint', _}, rest)) =>
      Endpoint.toEdge(endpoint).allowable = Allowed;
      Endpoint.toEdge(endpoint').allowable = Allowed;
      let queue =
        Label.assignT(
          ~v=Endpoint.toReverseVertex(nextEndpoint),
          ~p=nextEndpoint,
          ~mates,
          ~queue,
        );
      let nextEndpoint =
        switch (direction) {
        | Forward => endpoint'
        | Backward =>
          let Odd({endpoint, _}, _) = rest;
          Endpoint.reverse(endpoint);
        };
      Endpoint.toEdge(nextEndpoint).allowable = Allowed;
      relabelToBase(rest, nextEndpoint, queue, mates, direction);
    };

  /**
   * Expand the given top-level blossom.
   */
  let rec expand = (~graph, ~b, ~stage, ~mates, ~queue) => {
    let _debug_endstage =
      switch (stage) {
      | Endstage => "Endstage"
      | NotEndstage => "Not endstage"
      };
    [%log.debug
      "expandBlossom";
      ("Blossom", Blossom._debug(b));
      ("Endstage", _debug_endstage);
      ("Children", Child._debug(b.fields.children))
    ];
    /* Convert sub-blossoms into top-level blossoms. */
    let queue =
      Odd.reduceU(b.fields.children, ~init=queue, ~f=(. queue, child) =>
        switch (child.node) {
        | Vertex(v) as vertex =>
          v.fields.inBlossom = vertex;
          v.parent = None;
          queue;
        | Blossom(b) as blossom =>
          b.parent = None;
          switch (b, stage) {
          | ({dualVar: 0., _}, Endstage) =>
            /* Recursively expand this sub-blossom. */
            expand(~graph, ~b, ~stage, ~mates, ~queue)
          | (_, Endstage | NotEndstage) =>
            /* This sub-blossom is becoming a top-level blossom, so change its
               children's inBlossom to it. */
            Node.Leaves.forEachU(blossom, ~f=(. v) =>
              v.fields.inBlossom = blossom
            );
            queue;
          };
        }
      );
    let queue =
      switch (b.label, stage) {
      /* If we expand a T-blossom during a stage, its sub-blossoms must be
         relabeled. */
      | (T(labelEndpoint), NotEndstage) =>
        /* Start at the sub-blossom through which the expanding blossom obtained
           its label, and relabel sub-blossoms until we reach the base.
           Figure out through which sub-blossom the expanding blossom obtained
           its label initially. */
        let entryNode =
          Endpoint.toReverseVertex(labelEndpoint).fields.inBlossom;
        let (base, p, childrenToEntryChild, queue) =
          switch (splitChildren(b.fields.children, entryNode)) {
          /* If the base is the entry child, don't relabel to the base but do
             process the rest of the children. */
          | NoSplit({base, rest}) => (base.node, labelEndpoint, rest, queue)
          | GoForward({base, front, entry, back}) =>
            let (endpoint, queue) =
              relabelToBase(
                Odd(entry, Odd.concat(back, Odd.make(base))),
                labelEndpoint,
                queue,
                mates,
                Forward,
              );
            (base.node, endpoint, front, queue);
          | GoBackward({base, front, entry, back}) =>
            let (endpoint, queue) =
              relabelToBase(
                Odd(entry, Even.reverse(Even(base, front))),
                labelEndpoint,
                queue,
                mates,
                Backward,
              );
            (base.node, endpoint, back, queue);
          };
        /* Relabel the base T-sub-blossom WITHOUT stepping through to its mate.
         */
        Node.removeBestEdge(base);
        Label.assignTSingle(~w=base, ~p);
        Label.assignTSingleVertex(~v=Endpoint.toReverseVertex(p), ~p);
        /* Continue along the blossom until we get to the entry child. */
        Even.reduceU(childrenToEntryChild, ~init=queue, ~f=(. queue, child) => {
          /* Examine the vertices of the sub-blossom to see whether it is
             reachable from a neighboring S-vertex outside the expanding
             blossom. */
          switch (Node.label(child.node)) {
          /* This sub-blossom just got its label S through one of its neighbors;
             leave it. */
          | SingleS
          | S(_) => queue
          | Free
          | T(_) =>
            /* If the sub-blossom contains a reachable vertex, assign label T to
               the sub-blossom. */
            let rec labelReachableVertex = leaves =>
              switch (leaves) {
              | [] => queue
              | [v, ...rest] =>
                switch (v.label) {
                | Free => labelReachableVertex(rest)
                | T(p) => Label.assignT(~v, ~p, ~mates, ~queue)
                | SingleS
                | S(_) => failwith("Must be labeled Free or T.")
                }
              };
            child.node |> Node.Leaves.toList |> labelReachableVertex;
          }
        });

      /* Labels are erased at the end of a stage; no relabeling is necessary. */
      | (T(_), Endstage)
      | (Free | SingleS | S(_), Endstage | NotEndstage) => queue
      };
    graph.blossoms =
      Belt.List.keepU(graph.blossoms, (. x) => !Blossom.eq(b, x));
    queue;
  };
};

/*******************************************************************************
 * Part V: The main loop
 ******************************************************************************/

module Delta = {
  type t('v) =
    | One(float)
    | Two({
        delta: float,
        edge: Edge.t('v),
      })
    | Three({
        delta: float,
        edge: Edge.t('v),
      })
    | Four({
        delta: float,
        blossom: Blossom.t('v),
      });

  let _debug =
    fun
    | One(delta) => {j|1=$delta|j}
    | Two({delta, _}) => {j|2=$delta|j}
    | Three({delta, _}) => {j|3=$delta|j}
    | Four({delta, _}) => {j|4=$delta|j};

  let getMinDualVar = ({vertices, maxWeight, _}) =>
    Belt.List.reduceU(vertices, maxWeight, (. minDualVar, v) =>
      min(minDualVar, v.dualVar)
    );

  /**
   * Compute delta1: the minimum value of any vertex dual variable.
   */
  let one = (~cardinality, ~graph) =>
    switch (cardinality) {
    | `Max => None
    | `NotMax => Some(One(getMinDualVar(graph)))
    };

  /**
   * Compute delta2: the minimum slack on any edge between an S-vertex and a
   * free vertex.
   */
  let two = (deltaType, ~graph) =>
    Belt.List.reduceU(graph.vertices, deltaType, (. deltaType, v) =>
      switch (v.bestEdge, Node.label(v.fields.inBlossom)) {
      | (Some(edge), Free) =>
        let kslack = Edge.slack(edge);
        switch (deltaType) {
        | None => Some(Two({delta: kslack, edge}))
        | Some(
            One(delta) | Two({delta, _}) | Three({delta, _}) |
            Four({delta, _}),
          )
            when kslack < delta =>
          Some(Two({delta: kslack, edge}))
        | Some(One(_) | Two(_) | Three(_) | Four(_)) as deltaType => deltaType
        };
      | (_, Free | SingleS | S(_) | T(_)) => deltaType
      }
    );

  let threeHelper = (deltaType, node) =>
    switch (node) {
    | {parent: None, bestEdge: Some(edge), label: SingleS | S(_), _} =>
      let kslack = Edge.slack(edge) /. 2.;
      switch (deltaType) {
      | None => Some(Three({delta: kslack, edge}))
      | Some(
          One(delta) | Two({delta, _}) | Three({delta, _}) |
          Four({delta, _}),
        )
          when kslack < delta =>
        Some(Three({delta: kslack, edge}))
      | Some(One(_) | Two(_) | Three(_) | Four(_)) as deltaType => deltaType
      };
    | {label: Free | SingleS | S(_) | T(_), _} => deltaType
    };

  /**
   * Compute delta3: half the minimum slack on any edge between a pair of
   * S-blossoms.
   */
  let three = (deltaType, ~graph) => {
    let deltaType = Belt.List.reduce(graph.vertices, deltaType, threeHelper);
    Belt.List.reduce(graph.blossoms, deltaType, threeHelper);
  };

  /**
   * Compute delta4: minimum z variable of any T-blossom.
   */
  let four = (deltaType, ~graph) =>
    Belt.List.reduceU(graph.blossoms, deltaType, (. deltaType, b) =>
      switch (b) {
      | {parent: None, label: T(_), dualVar, _} =>
        switch (deltaType) {
        | None => Some(Four({delta: dualVar, blossom: b}))
        | Some(
            One(delta) | Two({delta, _}) | Three({delta, _}) |
            Four({delta, _}),
          )
            when dualVar < delta =>
          Some(Four({delta: dualVar, blossom: b}))
        | Some(One(_) | Two(_) | Three(_) | Four(_)) as deltaType => deltaType
        }
      | {label: Free | SingleS | S(_) | T(_), _} => deltaType
      }
    );

  let makeDelta = (~cardinality, ~graph) =>
    one(~cardinality, ~graph)
    |> two(~graph)
    |> three(~graph)
    |> four(~graph)
    |> {
      fun
      | Some(deltaType) => deltaType
      /* No further improvement possible; max-cardinality optimum reached.
         Do a final delta update to make the optimum verifiable. */
      | None => One(graph |> getMinDualVar |> max(0.));
    };
  /* Aliasing `make` and `makeDelta` for better JavaScript debugging. */
  let make = makeDelta;
};

module Substage = {
  /* Each iteration of the loop is a "substage." A substage tries to find an
     augmenting path. If found, the path is used to improve the matching and the
     stage ends. If there is no augmenting path, the primal-dual method is used
     to pump some slack out of the dual variables. */
  type t('v, 'id) =
    | Augmented(Mates.t('v, 'id))
    | NotAugmented({
        queue: list(Vertex.t('v)),
        mates: Mates.t('v, 'id),
      });

  /**
   * Match vertex `s` to remote endpoint `p`. Then trace back from `s` until we
   * find a single vertex, swapping matched and unmatched edges as we go.
   */
  let rec augmentMatchingLoop = (mates, ~s, ~p) => {
    let mates =
      switch (s.fields.inBlossom) {
      /* Augment through the S-blossom to the base. */
      | Blossom(b) => ModifyBlossom.augment(b, s, mates)
      | Vertex(_) => mates
      };
    /* Update `s`'s mate. */
    let mates = Mates.Internal.set(mates, s, p);
    /* Trace one step back. */
    switch (Node.label(s.fields.inBlossom)) {
    | Free
    | T(_) => failwith("Required S vertex.")
    | S(endpoint) =>
      let tInBlossom = Endpoint.toVertex(endpoint).fields.inBlossom;
      switch (Node.label(tInBlossom)) {
      | Free
      | SingleS
      | S(_) => failwith("Required T vertex.")
      | T(p) =>
        /* Trace one step back. */
        let s = Endpoint.toVertex(p);
        let j = Endpoint.toReverseVertex(p);
        let mates =
          switch (tInBlossom) {
          /* Augment through the T-blossom from `j` to base. */
          | Blossom(bt) => ModifyBlossom.augment(bt, j, mates)
          | Vertex(_) => mates
          };
        /* Update `j`'s mate. */
        let mates = Mates.Internal.set(mates, j, p);
        /* Keep the opposite endpoint. It will be assigned to `s`'s mate in the
           next step. */
        augmentMatchingLoop(mates, ~s, ~p=Endpoint.reverse(p));
      };
    /* Reached a single vertex; stop. */
    | SingleS => mates
    };
  };

  /**
   * Swap matched/unmatched edges over an alternating path between two single
   * vertices. The augmenting path runs through the edge which connects a pair
   * of S vertices.
   */
  let augmentMatching = (edge, mates) => {
    [%log.debug
      "augmentMatching";
      ("v", Vertex._debug(edge.i));
      ("w", Vertex._debug(edge.j))
    ];
    [%log.debug
      "PAIR";
      ("PAIR", (Vertex._debug(edge.i), Vertex._debug(edge.j)))
    ];
    mates
    ->augmentMatchingLoop(~s=edge.i, ~p=J(edge))
    ->augmentMatchingLoop(~s=edge.j, ~p=I(edge));
  };

  let scanNeighbors = (vertex, graph, mates, queue) => {
    let rec loop = (neighbors, queue) =>
      switch (neighbors) {
      | [] => NotAugmented({mates, queue})
      | [endpoint, ...neighbors] =>
        let edge = Endpoint.toEdge(endpoint);
        let neighbor = Endpoint.toVertex(endpoint);
        /* This edge is internal to a blossom; ignore it. */
        if (Node.eq(vertex.fields.inBlossom, neighbor.fields.inBlossom)) {
          loop(neighbors, queue);
        } else {
          let kslack = Edge.slack(edge);
          /* Edge has zero slack => it is allowable. */
          switch (edge.allowable) {
          | NotAllowed when kslack <= 0. => edge.allowable = Allowed
          | Allowed
          | NotAllowed => ()
          };
          switch (edge.allowable) {
          | Allowed =>
            switch (Node.label(neighbor.fields.inBlossom)) {
            /* (C1) neighbor is a free vertex; label with T and label its mate
               with S (R12). */
            | Free =>
              let queue =
                Label.assignT(
                  ~v=neighbor,
                  ~p=Endpoint.reverse(endpoint),
                  ~mates,
                  ~queue,
                );
              loop(neighbors, queue);
            /* (C2) neighbor is an S-vertex (not in the same blossom; follow
               back-links to discover either an augmenting path or a new
               blossom. */
            | SingleS
            | S(_) =>
              switch (AddBlossom.scanForBlossom(edge)) {
              /* Found a new blossom; add it to the blossom bookkeeping and
                 turn it into an S-blossom. */
              | AddBlossom.NewBlossom(children) =>
                let ParityList.Odd({node: _debug_node, _}, _) = children;
                [%log.debug
                  "addBlossom";
                  ("base", Node._debug(_debug_node));
                  ("v", Vertex._debug(edge.i));
                  ("w", Vertex._debug(edge.j))
                ];
                [%log.debug
                  "blossomChildren";
                  ("children", Child._debug(children))
                ];
                let queue = AddBlossom.make(graph, children, queue);
                loop(neighbors, queue);
              /* Found an augmenting path; augment the matching and end this
                 stage. */
              | AddBlossom.AugmentingPath =>
                Augmented(augmentMatching(edge, mates))
              }
            | T(_) =>
              switch (neighbor.label) {
              /* Neighbor is inside a T-blossom, but itself has not yet been
                 reached from outside the blossom; mark it as reached (we need
                 to relabel during T-blossom expansion). */
              | Free =>
                Label.assignTSingleVertex(
                  ~v=neighbor,
                  ~p=Endpoint.reverse(endpoint),
                );
                loop(neighbors, queue);
              | SingleS
              | S(_)
              | T(_) => loop(neighbors, queue)
              }
            }
          | NotAllowed =>
            switch (Node.label(neighbor.fields.inBlossom)) {
            | SingleS
            | S(_) =>
              /* Keep track of the least-slack non-allowable edge to a different
                 S-blossom. */
              switch (Node.bestEdge(vertex.fields.inBlossom)) {
              | None => Node.setBestEdge(vertex.fields.inBlossom, ~edge)
              | Some(bestEdge) when kslack < Edge.slack(bestEdge) =>
                Node.setBestEdge(vertex.fields.inBlossom, ~edge)
              | _ => ()
              };
              loop(neighbors, queue);
            | Free
            | T(_) =>
              switch (neighbor.label) {
              | Free =>
                /* Neighbor is a free vertex (or an unreached vertex inside a
                   T-blossom) but we cannot reach it yet; keep track of the
                   least-slack edge that reaches it. */
                switch (neighbor.bestEdge) {
                | None => neighbor.bestEdge = Some(edge)
                | Some(bestEdge) when kslack < Edge.slack(bestEdge) =>
                  neighbor.bestEdge = Some(edge)
                | _ => ()
                };
                loop(neighbors, queue);
              | SingleS
              | S(_)
              | T(_) => loop(neighbors, queue)
              }
            }
          };
        };
      };
    loop(vertex.fields.neighbors, queue);
  };

  /**
   * Continue labeling until all vertices which are reachable through an
   * alternating path have gotten a label.
   */
  let rec labelingLoop = (graph, mates, queue) =>
    switch (queue) {
    | [] => NotAugmented({queue, mates})
    | [vertex, ...queue] =>
      [%log.debug "POP"; ("Vertex", Vertex._debug(vertex))];
      switch (scanNeighbors(vertex, graph, mates, queue)) {
      | NotAugmented({queue, mates}) => labelingLoop(graph, mates, queue)
      | Augmented(_) as augmented => augmented
      };
    };

  let rec substage = (graph, queue, mates, cardinality) => {
    %log.debug
    "SUBSTAGE";
    switch (labelingLoop(graph, mates, queue)) {
    | NotAugmented({queue, mates}) =>
      /* There is no augmenting path under these constraints;
         compute delta and reduce slack in the optimization problem. */
      let delta = Delta.make(~cardinality, ~graph);
      /* Take action at the point where the minimum delta occurred. */
      [%log.debug "DELTA"; ("delta", Delta._debug(delta))];
      switch (delta) {
      /* No further improvement possible; optimum reached. */
      | Delta.One(delta) =>
        Graph.updateDualVarsByDelta(graph, ~delta);
        NotAugmented({queue, mates});
      /* Use the least-slack edge to continue the search. */
      | Delta.Two({delta, edge}) =>
        Graph.updateDualVarsByDelta(graph, ~delta);
        let nextVertex =
          switch (Node.label(edge.i.fields.inBlossom)) {
          | Free => edge.j
          | SingleS
          | S(_)
          | T(_) => edge.i
          };
        let queue = [nextVertex, ...queue];
        edge.allowable = Allowed;
        substage(graph, queue, mates, cardinality);
      /* Use the least-slack edge to continue the search. */
      | Delta.Three({delta, edge}) =>
        Graph.updateDualVarsByDelta(graph, ~delta);
        let queue = [edge.i, ...queue];
        edge.allowable = Allowed;
        substage(graph, queue, mates, cardinality);
      /* Expand the least-z blossom. */
      | Delta.Four({delta, blossom}) =>
        Graph.updateDualVarsByDelta(graph, ~delta);
        let queue =
          ModifyBlossom.expand(
            ~graph,
            ~b=blossom,
            ~stage=NotEndstage,
            ~queue,
            ~mates,
          );
        substage(graph, queue, mates, cardinality);
      };
    | Augmented(_) as augmented => augmented
    };
  };
  /* Aliasing `make` and `substage` for better JavaScript debugging. */
  let make = substage;
};

/**
 * Loop until no further improvement is possible.
 */
let rec mainLoop = (~graph, ~mates, ~cardinality, ~stageNum, ~stageMax) =>
  if (stageNum == stageMax) {
    mates;
  } else {
    [%log.debug {j|STAGE $stageNum|j}; ("Mates", Mates._debug(mates))];
    /* Each iteration of this loop is a "stage". A stage finds an augmenting
       path and uses that to improve the matching. */

    /* Remove labels, forget least-slack edges and allowable edges, and empty
       queue. */
    Belt.List.forEachU(
      graph.blossoms,
      (. b) => {
        b.bestEdge = None;
        b.fields.blossomBestEdges = [];
        b.label = Free;
      },
    );
    /* Loss of labeling means that we can not be sure that currently
       allowable edges remain allowable throughout this stage. */
    Belt.List.forEachU(graph.edges, (. k) => k.allowable = NotAllowed);
    /* Label all single blossoms/vertices with S and put them in the queue. */
    let queue =
      Belt.List.reduceU(
        graph.vertices,
        [],
        (. queue, v) => {
          /* Forget all about least-slack edges. */
          v.bestEdge = None;
          if (Mates.Internal.has(mates, v)) {
            v.label = Free;
            queue;
          } else {
            Label.assignS(~v, ~label=SingleS, ~queue);
          };
        },
      );

    switch (Substage.make(graph, queue, mates, cardinality)) {
    /* No further improvement is possible. */
    | Substage.NotAugmented({mates, _}) => mates
    /* End of a stage; expand all S-blossoms which have `dualVar` = 0. */
    | Substage.Augmented(mates) =>
      Belt.List.forEachU(graph.blossoms, (. b) =>
        switch (b) {
        | {parent: None, label: SingleS | S(_), dualVar: 0., _} =>
          ModifyBlossom.expand(~graph, ~b, ~stage=Endstage, ~mates, ~queue)
          |> ignore
        | {label: Free | SingleS | S(_) | T(_), _} => ()
        }
      );
      mainLoop(
        ~graph,
        ~mates,
        ~cardinality,
        ~stageNum=succ(stageNum),
        ~stageMax,
      );
    };
  };

/*******************************************************************************
 * Part VI: The public interface
 ******************************************************************************/

type t('v, 'id) = Mates.t('v, 'id);

let make = (~cardinality=`NotMax, edges, ~id, ~cmp) =>
  switch (edges) {
  /* Deal swiftly with empty graphs. */
  | [] => Mates.Internal.make(~id)
  | edges =>
    let graph = Graph.make(edges, ~id, ~cmp);
    mainLoop(
      ~graph,
      ~mates=Mates.Internal.make(~id),
      ~cardinality,
      ~stageNum=0,
      ~stageMax=graph.vertexSize,
    );
  };

let get = Mates.get;
let reduceU = Mates.reduceU;
let reduce = Mates.reduce;
let forEachU = Mates.forEachU;
let forEach = Mates.forEach;
let toList = Mates.toList;
let toMap = Mates.toMap;
let isEmpty = Mates.isEmpty;
let has = Mates.has;

/* Not a public functor, just a shortcut for packaging predefined functions
   namespaced by their own modules. */
module Make = (M: {
                 type t;
                 let cmp: (t, t) => int;
               }) => {
  module Cmp = Belt.Id.MakeComparable(M);
  let make = make(~id=(module Cmp), ~cmp=M.cmp);
};

module Int =
  Make({
    type t = int;
    let cmp: (t, t) => int = compare;
  });

module String =
  Make({
    type t = string;
    let cmp: (t, t) => int = compare;
  });
