# Re-Blossom 🌺

Re-Blossom is a [Reason](https://reasonml.github.io/) implementation of the
famous [blossom algorithm](https://en.wikipedia.org/wiki/Blossom_algorithm). It
finds a maximum matching of vertices on general, undirected, weighted graphs.

## Installation

You need familiarity with [Node.js](https://nodejs.org/) and npm (which comes
with Node.js) or Yarn package manager.

Re-Blossom requires [BuckleScript](https://bucklescript.github.io/) as a peer
dependency, so you will have to install it separately. Add it by running:
```sh
npm install bs-platform
```
For new projects, see BuckleScript's [guide for initializing a project](https://bucklescript.github.io/docs/en/new-project).
For existing projects, Re-Blossom requires BuckleScript 7 or later.

Now you can add Re-Blossom to your project by running:
```sh
npm install re-blossom
```

Finally, you will need to edit your project's
[`bsconfig.json` file](https://bucklescript.github.io/docs/en/build-configuration#docsNav)
and list Re-Blossom in the `bs-dependencies`.
```json
{
  "bs-dependencies": [
    "re-blossom"
  ]
}
```

## How it works

Matching along an undirected, weighted graph is notoriously difficult. The
blossom algorithm does the heavy lifting for us in O(n³) time. Let's look at a
simple example.

Suppose you have a list of chess players, `[Mary, Joseph, Matthew, Mark, Luke,
John, Peter, Andrew, James, Philip]`, and you want to pair them to compete in a
tournament round.

Your first step is to list all of your possible pairings.
```reason
[
  (Mary, Joseph),
  (Mary, Matthew),
  (Joseph, Matthew),
  (Joseph, Mark),
  (Matthew, Luke),
  (Mark, Luke),
  (Mary, Andrew),
  (Luke, Peter),
  (Peter, John),
  (Andrew, Philip),
  (Mark, James)
]
```

(Typically your list will be much longer, but this is just an illustration.)

Next, you will need to determine the *weight* of each pairing. This is a
floating-point number that indicates how desirable that pairing is.

```reason
[
  (Mary, Joseph, 40.),
  (Mary, Matthew, 40.),
  (Joseph, Matthew, 60.),
  (Joseph, Mark, 55.),
  (Matthew, Luke, 55.),
  (Mark, Luke, 50.),
  (Mary, Andrew, 15.),
  (Luke, Peter, 30.),
  (Peter, John, 10.),
  (Andrew, Philip, 10.),
  (Mark, James, 10.)
]
```

In graph theory, each of the people is a "vertex," and each pair of people is an
"edge." We can visualize it in 2D space.

```
  Andrew ---10--- Philip                  Peter
    |                                    /     \
   15                                  30       10
    |                                  /         \
   Mary ---40--- Matthew ---55---- Luke         John
      \          /                  /
       40      60                 50
        \      /                  /
         Joseph ------ 55 ----- Mark ----30---- James
```

Now we let the algorithm work its magic. It will find a series of edges that
have the highest possible combined weight, where no vertex is listed twice, and
where no vertex is without a mate. In this example, the result is:
```reason
[
  (Mary, Joseph),
  (Matthew, Luke),
  (Mark, James),
  (John, Peter),
  (Andrew, Philip)
]
```

Or when we visualize it:
```
  Andrew -------- Philip                  Peter
                                               \
                                                \
                                                 \
   Mary          Matthew --------- Luke         John
      \
       \
        \
         Joseph                 Mark ---------- James
```

Note that we couldn't use the edge with the highest weight because choosing it
would leave another vertex with no connections. We also have to use the two
edges with the lowest weights because we're committed to matching as many
vertices as possible.

As you can see, finding the *maximum* weighted matching is often unintuitive.
Imagine how much more difficult this becomes when you have dozens, or hundreds,
of people, and every person could be potentially matched with anyone else! 

## Usage

**[For full documentation, see the interface file.](/src/Match.rei)**

Your data can be any type, but suppose you're using `string` vertices.
```reason
let graph = [
  ("Mary", "Joseph", 40.),
  ("Mary", "Michael", 40.),
  ("Joseph", "Michael", 60.),
  ("Joseph", "Gabriel", 55.),
  ("Michael", "Raphael", 55.),
  ("Gabriel", "Raphael", 50.),
  ("Mary", "Paul", 15.),
  ("Raphael", "Peter", 30.),
  ("Peter", "John", 10.),
  ("Paul", "James", 10.),
  ("Gabriel", "Andrew", 30.),
];
```

You can match them with `Blossom.Match.String.make`.
```reason
let result = Blossom.Match.String.make(graph);
```

You can also use `Blossom.Match.Int.make` for integer vertices.

### Using the output

The algorithm returns a bi-directional map of each vertex to its mate vertex.

```reason
Blossom.Match.get(result, "Mary"); /* Some("Joseph") */
Blossom.Match.get(result, "Joseph"); /* Some("Mary") */
```

It's powered by `Belt.Map` under the hood. You can convert it to a proper
`Belt.Map` with `toMap`, or a list with `toList`. _The output of these will have
each pairing twice._ This is because it treats each order (`(a, b)` vs `(b, a)`)
separately. In practice, this is useful so you can use `Belt.Map.get` or
`Belt.List.getAssoc` to get any vertex's mate.

### Maximum cardinality

The `make` functions accept one optional parameter, `cardinality`, which can
accept the value `` `Max ``. This enables "maximum cardinality" matching, where
the algorithm will only accept solutions that use as many edges as possible,
even extremely undesirable ones (such as ones with negative weights).

```reason
let graph = [
  (1, 2, 2.),
  (1, 3, (-2.)),
  (2, 3, 1.),
  (2, 4, (-1.)),
  (3, 4, (-6.)),
];

Blossom.Match.Int.make(graph);
/* [(1, 2)] */

Blossom.Match.Int.make(~cardinality=`Max, graph);
/* [(1, 3), (2, 4)] */
```

### Your own types

To use your own type, first you need a module that conforms to the
`Belt.Id.comparable` signature.

```reason
module MyType: {
  type t;
  let cmp: (t, t) => int;
} = { /* implementation goes here */ };

module MyTypeCmp = Belt.Id.MakeComparable(MyType);
```

Now you can call `Blossom.Match.make` with the `Id` module, the `cmp`function,
and your list of edges.

```reason
let result = Blossom.Match.make(~id=(module MyTypeCmp), ~cmp=MyType.cmp, graph);
```

## Beta warning

This algorithm passes all of the tests from similar implementations, but hasn't
seen much real-world use. There may still be failure states that have not been
discovered yet. The specific dangers are `Failure` exceptions, infinite loops,
or missing pairings. These should never happen, but, if they do, please
[file an issue](https://github.com/johnridesabike/re-blossom/issues) with
information about your graph.

This code uses BuckleScript-specific optimizations so it can compile to
efficient JavaScript. In the future, it may support other platforms as well.

## Similar packages

### JavaScript

The [edmonds-blossom](https://www.npmjs.com/package/edmonds-blossom)
package uses the same algorithm. It should return the exact same pairings that
this version does, but it doesn't have the flexibility of using different
types.

### Python

[Joris van Rantwijk's Python implementation](http://jorisvr.nl/article/maximum-matching)
was the basis of both the JavaScript version and this Reason version. 


## Changelog

### 1.0.2

- Added package description.

### 1.0.1

- Initial release.

## Development

Download the code:
```sh
git clone https://github.com/johnridesabike/re-blossom.git
```
If you want to make your own changes, then it's recommended to fork the
repository on GitHub and clone your forked version.

Install the dependencies:
```sh
npm install
```

Compile a production build:
```sh
npm run build
```

Run the Reason watcher (not necessary if your IDE automatically compiles
Reason):
```sh
npm run start
```

Run the tests:
```sh
npm run test
```

Run the tests and generate coverage (JavaScript coverage only):
```sh
npm run test:coverage
```

Run benchmarks that compare it to the similar JavaScript algorithm:
```sh
npm run bench
```

Run benchmarks in a browser:
```sh
npm run browser
```
Then open the URL provided and navigate to the `__benchmarks__` directory.

To turn on debug logging, enable [bs-log](https://github.com/MinimaHQ/bs-log)
with the `BS_LOG` environmental variable:
```sh
BS_LOG=re-blossom=* npm run build

# or with your editor

BS_LOG=re-blossom=* vim
```

When reading the code, you may need familiarity with BuckleScript's
[uncurrying](https://bucklescript.github.io/docs/en/function#solution-guaranteed-uncurrying),
as well as its map and set structures.

## Credits

[Joris van Rantwijk's](http://jorisvr.nl/) Python code was an invaluable
reference. I can't take any credit for the algorithm itself. It exists thanks to
many people much smarter than me.
