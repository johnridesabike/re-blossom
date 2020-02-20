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
  Preface
 ******************************************************************************/
/**
  Weighted maximum matching in general graphs.

  This code was based heavily on a Python implementation by Joris van Rantwijk,
  who had consulted a C implementation by Ed Rothberg.

  Joris's comment from his version:

  > The algorithm is taken from "Efficient Algorithms for Finding Maximum
  > Matching in Graphs" by Zvi Galil, ACM Computing Surveys, 1986. It is based
  > on the "blossom" method for finding augmenting paths and the "primal-dual"
  > method for finding a matching of maximum weight, both due to Jack Edmonds.
  > Some ideas came from the "Implementation of algorithms for maximum matching
  > in non-bipartite graphs" by H.J. Gabow, Standford Ph.D. thesis, 1973.
  >
  > Many terms used in the comments (sub-blossom, T-vertex) come from the paper
  > by Galil; read the paper before reading this code.

  Thanks to Reason's strong typing and some clever ADTs, this version of this
  algorithm is almost entirely safe. Yet, there remain a few exceptional cases
  that are difficult to represent on a type level.

  Safe labeling is still unsolved. Labels must conform to a pattern (T->S) but
  the current types do not enforce it. This problem is complicated by the fact
  that each vertex's label is usually determined by its top-level parent
  blossom's label, not its own. The dynamic nature of these variables makes it
  a challenge to enfoce labels in an efficient way.

  Performance isn't everything, but it is a significant consideration.

  This code uses features from the BuckleScript compiler to output efficient
  JavaScript. It will require modification to compile on other platforms.
 */
/*******************************************************************************
  Part I: The types
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
      loop(Odd(head, Empty), tail);
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
 * Edges represent a connection between two vertices and a weight. They are not
 * modified by the algorithm once created.
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
 * Endpoints represent where an edge connects with a vertex; `I(edge)` is
 * equivalent to the vertex at `edge.i`.
 */
and endpoint('v) =
  | I(edge('v))
  | J(edge('v))
and basicNode('v, 'content, 'fields) = {
  /* For a vertex, this is the data recieved from the input. It can be any type.
     for a blossom, it is an int. */
  content: 'content,
  /* The node's immediate parent (sub-)blossom, or `None` if the vertex is a
     top-level blossom. */
  mutable parent: option(blossom('v)),
  /* The node's veriable in the dual optimization problem. */
  mutable dualVar: float,
  /* If the node is free (or unreached inside a T-blossom), its best edge is
     the edge to an S-vertex with least slack, or `None` if there is no such
     edge.
     If it is a (possibly trivial) top-level S-blossom, its best edge is the
     least-slack edge to a different S-blossom, or `None` if there is no
     such edge.
     This is used for efficient computation of delta-two and delta-three. */
  mutable bestEdge: option(edge('v)),
  /* The label of the node is found by looking at the label of its top-level
     containing blososm. If the node is inside a T-blossom, its label is T
     if it is reachable from an S-vertex outside the blossom.
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
  /* The blossom's base vertex, the head of its list of children. */
  mutable base: vertex('v),
  /* A list of the blossom's sub-blossoms, starting with the base and going
     around the blossom. */
  mutable children: ParityList.Odd.t(child('v)),
  /* A list of least-slack edges to neighboring S-blossoms. This is used for
     efficient computation of delta-three. */
  /* We're using an association list to map nodes to edges. There are
     probably more efficient structures we could use, like maps, but this
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
 * from outside the blososm.
 */
and label('v) =
  | Free
  | SingleS /* Only assigned when a stage begins. */
  | S(endpoint('v))
  | T(endpoint('v));

module Edge = {
  type t('v) = edge('v);

  /**
   * Returns the slack of the given. (Does not work inside blossoms.)
   */
  let slack = k => k.i.dualVar +. k.j.dualVar -. k.weight;

  let _debug = k => {
    let i = k.i.content;
    let j = k.j.content;
    let w = k.weight;
    {j|{i: $i, j: $j, weight: $w}|j};
  };
};

/*******************************************************************************
  Part II: Accessors and utility functions
 ******************************************************************************/

module Endpoint = {
  type t('v) = endpoint('v);

  let toEdge = (J(edge) | I(edge)) => edge;

  let toVertex =
    fun
    | I(edge) => edge.i
    | J(edge) => edge.j;

  let toReverseVertex =
    fun
    | I(edge) => edge.j
    | J(edge) => edge.i;

  let reverse =
    fun
    | I(edge) => J(edge)
    | J(edge) => I(edge);

  let _debug =
    fun
    | I(edge) => "I(" ++ Edge._debug(edge) ++ ")"
    | J(edge) => "J(" ++ Edge._debug(edge) ++ ")";
};

module Vertex = {
  type t('v) = vertex('v);

  /* We can use reference equality (===) even though we don't know the vertex
     types because they never change after the graph is created. */
  let eq = (a, b) => a.content === b.content;

  let _debug: t('v) => string = v => Js.String.make(v.content);
};

module Blossom = {
  type t('v) = blossom('v);

  let eq: (t('v), t('v)) => bool = (a, b) => a.content == b.content;
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
     * Generate the leafs of a node. Leaves contain the vertices in a blossom's
     * children, as well as the vertices in any sub-blossom's children.
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
    ParityList.Odd.reduceU(c, ~init=[||], ~f=(. acc, child) =>
      Belt.Array.concat(acc, [|Node._debug(child.node)|])
    );
};

module Mates = {
  /* Maps vertices to remote endpoints of their attached edges.
     Initially, all vertices are single. */
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
};

module Label = {
  let _debug =
    fun
    | Free => "Free"
    | SingleS => "SingleS"
    | S(endpoint) => "S(" ++ Endpoint._debug(endpoint) ++ ")"
    | T(endpoint) => "T(" ++ Endpoint._debug(endpoint) ++ ")";

  /**
   * Since it became an S-vertex/blossom, add its child vertices to the
   * queue.
   */
  let assignS = (~v, ~label, ~queue) => {
    [%log.debug
      "assignLabel";
      ("w", Vertex._debug(v));
      ("t", _debug(label))
    ];
    let b = v.fields.inBlossom;
    switch (b) {
    | Blossom(b) =>
      b.label = label;
      b.bestEdge = None;
    | Vertex(_) => v.bestEdge = None
    };
    v.bestEdge = None;
    v.label = label;
    [%log.debug "PUSH"; ("PUSH", Node.Leaves._debug(b))];
    Node.Leaves.toList(b, ~init=queue);
  };

  /**
   *`v` became a T-Vertex. Its mate will be labeled S.
   */
  let assignT = (~v, ~p, ~mates) => {
    [%log.debug
      "assignLabel";
      ("w", Vertex._debug(v));
      ("t", _debug(T(p)))
    ];
    let b = v.fields.inBlossom;
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
   * Label a blossom T without stepping through to its mate.
   */
  let assignTSingleBlossom = (~b, ~p) => b.label = T(p);

  /**
   * Label a vertex or blossom T without stepping through to its mate.
   */
  let assignTSingle = (~w, ~p) =>
    switch (w) {
    | Vertex(v) => assignTSingleVertex(~v, ~p)
    | Blossom(b) => assignTSingleBlossom(~b, ~p)
    };
};

/*******************************************************************************
  Part III: Let's start making a graph
 ******************************************************************************/

module Graph = {
  type t('v) = graph('v);

  /**
   * Turn the raw input into a recursive graph.
   */
  let makeGraph =
      (type v, type id, rawEdges, ~id: Belt.Id.comparable(v, id), ~cmp) => {
    /* We need to be able to validate the input and identify duplicate vertices
       and edges. This set and map will help us do it efficiently. */
    let cmpU = (. a, b) => cmp(a, b);
    module Id = (val id);
    /* Create a set of tuples to store the pairs of vertices in each edge. */
    module EdgeCmp =
      Belt.Id.MakeComparableU({
        type t = (Id.t, Id.t);
        let cmp =
          (. (a, b), (y, z)) =>
            switch (cmpU(. a, y), cmpU(. b, z)) {
            | (0, 0) => 0
            | _ =>
              switch (cmpU(. a, z), cmpU(. b, y)) {
              | (0, 0) => 0
              | (c, d) =>
                switch (c + d) {
                | 0 => c
                | e => e
                }
              }
            };
      });
    let edgeSet = Belt.Set.make(~id=(module EdgeCmp));
    /* Create a map of each vertex to its content type. */
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
        if (cmpU(. iId, jId) == 0 || Belt.Set.has(edgeSet, (iId, jId))) {
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
          let edgeSet = Belt.Set.add(edgeSet, (iId, jId));
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
              ~vertexSize=vertexSize->succ->succ,
              ~maxWeight,
            );
          };
        }
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
  /* Aliasing `make` and `makeGraph` for better JS debugging. */
  let make = makeGraph;

  let updateDualVarsByDelta = (graph, ~delta) => {
    Belt.List.forEachU(graph.vertices, (. v) =>
      v.dualVar = (
        switch (Node.label(v.fields.inBlossom)) {
        /* S-vertex: u = u - delta*/
        | SingleS
        | S(_) => v.dualVar -. delta
        /* T-vertex: u = u + delta*/
        | T(_) => v.dualVar +. delta
        | Free => v.dualVar
        }
      )
    );
    Belt.List.forEachU(graph.blossoms, (. b) =>
      switch (b) {
      | {parent: None, label: SingleS | S(_), _} =>
        /* top-level S-blossom: z = z + delta */
        b.dualVar = b.dualVar +. delta
      | {label: T(_), _} =>
        /* top-level T-blossom: z = z - delta */
        b.dualVar = b.dualVar -. delta
      | {parent: Some(_), _}
      | {label: Free, _} => ()
      }
    );
  };
};

/*******************************************************************************
  Part IV: Add, augment, and expand blossoms
 ******************************************************************************/

module AddBlossom = {
  /* First, we have to scan to see if we are able to add a blossom. */
  type traceResult('v, 'a) =
    | DeadEnd('a)
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
    | SingleS => DeadEnd(backChildren)
    | T(_) => failwith("Label should only be S")
    | S(p) =>
      let w2 = Endpoint.toVertex(p).fields.inBlossom;
      switch (Node.label(w2)) {
      | Free
      | SingleS
      | S(_) => failwith("Label should only be T")
      | T(p2) =>
        let backChildren =
          ParityList.Infix.(
            backChildren
            <:> {node: w, endpoint: Endpoint.reverse(p)}
            <.> {node: w2, endpoint: Endpoint.reverse(p2)}
          );
        let nextW = Endpoint.toVertex(p2).fields.inBlossom;
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
    | SingleS => DeadEnd(frontChildren)
    | T(_) => failwith("Label should only be S")
    | S(p) =>
      let v2 = Endpoint.toVertex(p).fields.inBlossom;
      switch (Node.label(v2)) {
      | Free
      | SingleS
      | S(_) => failwith("Label should only be T")
      | T(p2) =>
        let lastV = Endpoint.toVertex(p2).fields.inBlossom;
        let frontChildren =
          ParityList.Infix.(
            frontChildren
            <.> {node: v2, endpoint: p}
            <:> {node: lastV, endpoint: p2}
          );
        FoundChild(lastV, frontChildren);
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
    open Node.Infix;

    let initialV = edge.i.fields.inBlossom;
    let initialW = edge.j.fields.inBlossom;

    let rec loop = (front, back) =>
      switch (front, back) {
      | (DeadEnd(_), DeadEnd(_)) => AugmentingPath
      | (DeadEnd(frontChildren), FoundChild(nextW, backChildren)) =>
        let Odd({node: child, _}, _) = frontChildren;
        /* The first front child was a SingleS, the back traced around to it. */
        if (child =|= nextW) {
          NewBlossom(frontChildren);
        } else {
          loop(front, traceBackward(nextW, backChildren));
        };
      | (FoundChild(lastV, frontChildren), DeadEnd(backChildren)) =>
        let lastW =
          switch (backChildren) {
          | Empty => initialW
          | Even({node, _}, _) => node
          };
        /* The first back child was a SingleS, the front traced around to it. */
        if (lastV =|= lastW) {
          NewBlossom(frontChildren);
        } else {
          loop(traceForward(lastV, frontChildren), back);
        };
      | (FoundChild(lastV, frontChildren), FoundChild(nextW, backChildren))
          when lastV =|= nextW =>
        NewBlossom(
          Odd.concatEven(frontChildren, Even.reverse(backChildren)),
        )
      | (FoundChild(lastV, frontChildren), FoundChild(nextW, backChildren)) =>
        switch (traceBackward(nextW, backChildren)) {
        | FoundChild(nextW, backChildren) when lastV =|= nextW =>
          NewBlossom(
            Odd.concatEven(frontChildren, Even.reverse(backChildren)),
          )
        | (DeadEnd(_) | FoundChild(_)) as back =>
          loop(traceForward(lastV, frontChildren), back)
        }
      };
    loop(
      /* Manually add the i child to connect the two lists. */
      FoundChild(initialV, Odd.make({node: initialV, endpoint: I(edge)})),
      FoundChild(initialW, Empty),
    );
  };

  /* Now we can create a blossom. */

  let bestEdgesReducerHelper = (b, w, bestEdgeList, edge) =>
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

  let computeBestEdges = b => {
    let endpointReducer =
      (. bestEdgeList, endpoint) => {
        let neighbor = Endpoint.toVertex(endpoint).fields.inBlossom;
        let edge = Endpoint.toEdge(endpoint);
        bestEdgesReducerHelper(b, neighbor, bestEdgeList, edge);
      };

    let edgeReducer =
      (. bestEdgeList, (_node, edge)) => {
        let neighbor =
          Node.eqB(edge.j.fields.inBlossom, b)
            ? edge.i.fields.inBlossom : edge.j.fields.inBlossom;
        bestEdgesReducerHelper(b, neighbor, bestEdgeList, edge);
      };

    ParityList.Odd.reduceU(
      b.fields.children,
      ~init=[],
      ~f=(. bestEdgeList, child) => {
        let bestEdgeList =
          switch (child.node) {
          /* This subblossom does not have a list of least-slack edges; get
             the information from the vertices. */
          | Blossom({fields: {blossomBestEdges: [], _}, _}) as node
          | Vertex(_) as node =>
            Node.Leaves.reduceU(
              node, ~init=bestEdgeList, ~f=(. bestEdgeList, v) => {
              Belt.List.reduceU(
                v.fields.neighbors,
                bestEdgeList,
                endpointReducer,
              )
            })
          /* Walk this sub-blossom's least-slack edges. */
          | Blossom({fields: {blossomBestEdges, _}, _}) =>
            Belt.List.reduceU(blossomBestEdges, bestEdgeList, edgeReducer)
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
  };

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
  /* Aliasing `make` and `makeBlossom` for better JS debugging. */
  let make = makeBlossom;
};

module ModifyBlossom = {
  open ParityList;
  open Infix;
  /* When augmenting or expanding a blossom, we'll need to separate the base
     child, the "entry" child, and the list of children between them. Whether
     the entry child was odd or even will determine whether we go forward or
     backward. */
  type splitChildsDir('a) =
    | NoSplit
    | GoForward('a, Even.t('a), 'a, Odd.t('a))
    | GoBackward('a, Odd.t('a), 'a, Even.t('a));

  type direction =
    | Backward
    | Forward;

  let splitChildren = (childs, entryChild) => {
    open Node.Infix;
    let Odd(base, childs) = childs;
    let rec loop = (frontChilds, backChilds) =>
      switch (backChilds) {
      | Empty => /* base.child == entryChild */ NoSplit
      | Even(c1, tail) when c1.node =|= entryChild =>
        GoForward(base, Even.reverse(frontChilds), c1, tail)
      | Even(c1, Odd(c2, tail)) when c2.node =|= entryChild =>
        GoBackward(base, Odd.reverse(frontChilds <:> c1), c2, tail)
      | Even(c1, Odd(c2, tail)) => loop(frontChilds <:> c1 <.> c2, tail)
      };
    loop(Empty, childs);
  };

  let rec bubbleBlossomTree = (node, parent, b) =>
    switch (parent) {
    | None => failwith("There should be a parent.")
    | Some(parent) when Blossom.eq(parent, b) => node
    | Some(parent) => bubbleBlossomTree(Blossom(parent), parent.parent, b)
    };

  /**
   * Swap matched/unmached edges over an alternating path through a blossom
   * between vertex `v` and the base vertex. Keep blossom bookkeeping
   * consistent.
   */
  let rec augment = (b, v, mates) => {
    [%log.debug "augmentBlossom"; ("v", Vertex._debug(v))];
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
    let loopData =
      switch (splitChildren(b.fields.children, t)) {
      | NoSplit => None
      | GoForward(base, frontChilds, entryChild, backChilds) =>
        let moveList = Odd.concat(backChilds, Odd.make(base));
        let direction = Forward;
        let children =
          Odd(entryChild, Odd.concat(backChilds, Odd(base, frontChilds)));
        Some((moveList, direction, children));
      | GoBackward(base, frontChilds, entryChild, backChilds) =>
        let moveList = Even.reverse(Even(base, frontChilds));
        let direction = Backward;
        let children =
          Odd(entryChild, Even.concat(backChilds, Even(base, frontChilds)));
        Some((moveList, direction, children));
      };
    switch (loopData) {
    | None => mates
    | Some((moveList, direction, children)) =>
      b.fields.children = children;
      b.fields.base = v;
      let rec loopToBase = (children, mates, direction) =>
        switch (children) {
        | Empty => mates
        | Even(c1, Odd(c2, rest)) =>
          let p =
            switch (direction) {
            | Forward => c1.endpoint
            | Backward => Endpoint.reverse(c2.endpoint)
            };
          let mates =
            switch (c1.node) {
            /* Step into the next sub-blossom and augment it recursively. */
            | Blossom(b) => augment(b, Endpoint.toVertex(p), mates)
            | Vertex(_) => mates
            };
          let mates =
            switch (c2.node) {
            /* Step into the next sub-blossom and augment it recursively. */
            | Blossom(b) => augment(b, Endpoint.toReverseVertex(p), mates)
            | Vertex(_) => mates
            };
          /* Match the edge connecting those sub-blossoms. */
          let mates = Mates.Internal.setEdge(mates, Endpoint.toEdge(p));
          loopToBase(rest, mates, direction);
        };
      loopToBase(moveList, mates, direction);
    };
  };

  let rec relabelLoopToBase =
          (childsToBase, nextEndpoint, queue, mates, direction) =>
    switch (childsToBase) {
    | Odd({node, _}, Empty) => (node, queue, nextEndpoint)
    | Odd(
        {node: child1, endpoint: endpoint1},
        Even({endpoint: endpoint2, _}, rest),
      ) =>
      Endpoint.toEdge(endpoint1).allowable = Allowed;
      Endpoint.toEdge(endpoint2).allowable = Allowed;
      let queue =
        Label.assignT(~v=Node.base(child1), ~p=nextEndpoint, ~mates, ~queue);
      let nextEndpoint =
        switch (direction) {
        | Backward => endpoint2
        | Forward =>
          let Odd({endpoint, _}, _) = rest;
          Endpoint.reverse(endpoint);
        };
      Endpoint.toEdge(nextEndpoint).allowable = Allowed;
      relabelLoopToBase(rest, nextEndpoint, queue, mates, direction);
    };

  /**
   * Expand the given top-level blossom.
   */
  let rec expand = (~graph, ~b, ~stage, ~mates, ~queue) => {
    [%log.debug
      "expandBlossom";
      ("b", b.content);
      ("endstage", stage);
      ("children", Child._debug(b.fields.children))
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
          /* Recursively expand this sub-blossom */
          switch (b, stage) {
          | ({dualVar: 0., _}, Endstage) =>
            expand(~graph, ~b, ~stage, ~mates, ~queue)
          | (_, Endstage | NotEndstage) =>
            /* This sub-blossom is becoming a top-level blossom, so change its
               children's inblossom to it. */
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
           its label, and relabel sub-blossoms until we reach the base. */
        /* Figure out through which sub-blossom the expanding blossom obtained
           its label initially. */
        let entryChild =
          Endpoint.toReverseVertex(labelEndpoint).fields.inBlossom;
        let (childrenToBase, childrenToEntryChild, direction) =
          switch (splitChildren(b.fields.children, entryChild)) {
          | NoSplit => failwith("Entry child cannot be the base child.")
          | GoForward(base, front, entry, back) => (
              Odd(entry, Odd.concat(back, Odd.make(base))),
              front,
              Forward,
            )
          | GoBackward(base, front, entry, back) => (
              Odd(entry, Even.reverse(Even(base, front))),
              back,
              Backward,
            )
          };
        let (base, queue, p) =
          relabelLoopToBase(
            childrenToBase,
            labelEndpoint,
            queue,
            mates,
            direction,
          );
        /* Relabel the base T-sub-blossom WITHOUT stepping through to its mate
           (so don't call AssignLabel.t, call AssignLabel.tSingle instead.) */
        Node.removeBestEdge(base);
        Label.assignTSingle(~w=base, ~p);
        Label.assignTSingleVertex(~v=Endpoint.toReverseVertex(p), ~p);
        /* Continue along the blossom until we get to the entry child*/
        Even.reduceU(childrenToEntryChild, ~init=queue, ~f=(. queue, child) => {
          /* Examine the vertices of the sub-blosso to see whether it is
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
                | SingleS
                | S(_) => failwith("Must be labeled Free or T.")
                | T(p) => Label.assignT(~v, ~p, ~mates, ~queue)
                }
              };
            child.node->Node.Leaves.toList->labelReachableVertex;
          }
        });

      /* Labels are erased at the end of a stage, so no relabling is necessary*/
      | (T(_), Endstage)
      | (Free | SingleS | S(_), Endstage | NotEndstage) => queue
      };
    graph.blossoms =
      Belt.List.keepU(graph.blossoms, (. x) => !Blossom.eq(b, x));
    queue;
  };
};

/*******************************************************************************
  Part V: The main loop
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
   * Compute delta-one: the minumum value of any vertex dual.
   */
  let one = (~cardinality, ~graph) =>
    switch (cardinality) {
    | `Max => None
    | `NotMax => Some(One(getMinDualVar(graph)))
    };

  /**
   * Compute delta-two: the minimum slack on any edge between an S-vertex and a
   * free vertex.
   */
  let two = (deltaType, ~graph) =>
    Belt.List.reduceU(graph.vertices, deltaType, (. deltaType, v) =>
      switch (v.bestEdge, Node.label(v.fields.inBlossom)) {
      | (Some(edge), Free) =>
        let kslack = Edge.slack(edge);
        [%log.debug "delta2"; ("d", kslack)];
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
   * Compute delta-three: half the minimum slack on any edge between a pair of
   * S-blossoms
   */
  let three = (deltaType, ~graph) => {
    let deltaType = Belt.List.reduce(graph.vertices, deltaType, threeHelper);
    Belt.List.reduce(graph.blossoms, deltaType, threeHelper);
  };

  /**
   * Compute delta-four: minimum z variable of any T-blossom.
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

  let makeDelta = (~cardinality, graph) => {
    let deltaType =
      one(~cardinality, ~graph)->two(~graph)->three(~graph)->four(~graph);
    switch (deltaType) {
    | None =>
      /* No further improvement possible; max-cardinality optimum reached. Do a
         final delta update to make the optimum verifyable. */
      let minDualVar = getMinDualVar(graph);
      One(minDualVar > 0. ? minDualVar : 0.);
    | Some(deltaType) => deltaType
    };
  };
  /* Aliasing make and makeDelta for better JS debugging. */
  let make = makeDelta;
};

module Substage = {
  /* Each iteration of the loop is a "substage." A substage tries to find an
     augmenting path; if found, the path is used to improve the matching and the
     stage ends. If there is no augmenting path, the primal-dual method is used
     to pump some slack out of the dual variables. */
  type t('v, 'id) =
    | Augmented({
        graph: Graph.t('v),
        queue: list(Vertex.t('v)),
        mates: Mates.t('v, 'id),
      })
    | NotAugmented({
        graph: Graph.t('v),
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
      | Blossom(bs) => ModifyBlossom.augment(bs, s, mates)
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
          /*Augment through the T-blossom from `j` to base. */
          | Blossom(bt) => ModifyBlossom.augment(bt, j, mates)
          | Vertex(_) => mates
          };
        /* Update `j`'s mate. */
        let mates = Mates.Internal.set(mates, j, p);
        /* Keep the opposite endpoint;
           it will be assigned to `s`'s mate in the next step. */
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
      | [] => NotAugmented({mates, queue, graph})
      | [endpoint, ...neighbors] =>
        let edge = Endpoint.toEdge(endpoint);
        let neighbor = Endpoint.toVertex(endpoint);
        /* This edge is internal to a blossom; ignore it. */
        if (Node.eq(vertex.fields.inBlossom, neighbor.fields.inBlossom)) {
          loop(neighbors, queue);
        } else {
          let kslack = Edge.slack(edge);
          /* Edge has zero slack => it is allowable*/
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
                let mates = augmentMatching(edge, mates);
                Augmented({queue, graph, mates});
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
              | SingleS /* Path not taken? */
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
   * alternating path have got a label.
   */
  let rec labelingLoop = (graph, mates, queue) => {
    /* Take an S-vertex from the queue. */
    switch (queue) {
    | [] => NotAugmented({queue, mates, graph})
    | [vertex, ...queue] =>
      [%log.debug "POP"; ("POP v", Vertex._debug(vertex))];
      switch (scanNeighbors(vertex, graph, mates, queue)) {
      | NotAugmented({queue, mates, graph}) =>
        labelingLoop(graph, mates, queue)
      | Augmented(_) as augmented => augmented
      };
    };
  };

  let rec substage = (graph, queue, mates, cardinality) => {
    %log.debug
    "SUBSTAGE";
    switch (labelingLoop(graph, mates, queue)) {
    | NotAugmented({queue, mates, graph}) =>
      /* There is no augmenting path under these constraints;
         compute delta and reduce slack in the optimization problem. */
      let deltaType = Delta.make(~cardinality, graph);
      /* Take action at the point where the minimum delta occurred. */
      [%log.debug "delta"; ("delta", Delta._debug(deltaType))];
      switch (deltaType) {
      /*No further improvement possible; optimim reached. */
      | Delta.One(delta) =>
        Graph.updateDualVarsByDelta(graph, ~delta);
        NotAugmented({queue, mates, graph});
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
  /* Aliasing `make` and `substage` for better JS debugging. */
  let make = substage;
};

/**
 * Loop until no further improvement is possible.
 */
let rec mainLoop = (~graph, ~mates, ~cardinality, ~stageNum, ~stageMax) =>
  if (stageNum == stageMax) {
    mates;
  } else {
    [%log.debug "STAGE"; ("STAGE", stageNum)];
    /* Each iteration of this loop is a "stage". A stage finds an augmenting
       path and uses that to improve the matching. */

    /* gremove labels, forget least-slack edges and allowable edges, and empty
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
       allowable edges remain allowable througout this stage. */
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
    | Substage.NotAugmented({mates, _}) => mates
    | Substage.Augmented({queue, graph, mates}) =>
      /* End of a stage; expand all S-blossoms which have dualVar = 0. */
      Belt.List.forEachU(graph.blossoms, (. b) =>
        switch (b) {
        | {parent: None, label: SingleS | S(_), dualVar: 0., _} =>
          ModifyBlossom.expand(~graph, ~b, ~stage=Endstage, ~mates, ~queue)
          ->ignore
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
  Part VI: The public interface
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
