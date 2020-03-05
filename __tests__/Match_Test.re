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
open Jest;
open Expect;

let sortResult = (cmp, l) =>
  Belt.List.sort(l, ((a, _), (b, _)) => cmp(a, b));

describe("Trivial cases", () => {
  test("Empty input graph", () =>
    Match.Int.make([]) |> Match.toList |> expect |> toEqual([])
  );
  test("Single edge", () =>
    Match.Int.make([(0, 1, 1.)])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(0, 1), (1, 0)])
  );
  test("Two edges", () =>
    Match.Int.make([(1, 2, 10.), (2, 3, 11.)])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(2, 3), (3, 2)])
  );
  test("Three edges", () =>
    Match.Int.make([(1, 2, 5.), (2, 3, 11.), (3, 4, 5.)])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(2, 3), (3, 2)])
  );
  test("Three edges again, with IDs ordered differently", () =>
    Match.Int.make([(1, 2, 5.), (2, 3, 11.), (4, 3, 5.)])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(2, 3), (3, 2)])
  );
  test("Maximum cardinality", () =>
    Match.Int.make(
      [(1, 2, 5.), (2, 3, 11.), (3, 4, 5.)],
      ~cardinality=`Max,
    )
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(1, 2), (2, 1), (3, 4), (4, 3)])
  );
  test("Floating point weights", () =>
    Match.Int.make([
      (1, 2, Js.Math._PI),
      (2, 3, Js.Math.exp(1.)),
      (1, 3, 3.0),
      (1, 4, Js.Math.sqrt(2.0)),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(1, 4), (2, 3), (3, 2), (4, 1)])
  );
  describe("Negative weights", () => {
    test("Negative weights", () =>
      Match.Int.make([
        (1, 2, 2.),
        (1, 3, (-2.)),
        (2, 3, 1.),
        (2, 4, (-1.)),
        (3, 4, (-6.)),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 2), (2, 1)])
    );

    test("Negative weights with maximum cardinality", () =>
      Match.Int.make(
        ~cardinality=`Max,
        [
          (1, 2, 2.),
          (1, 3, (-2.)),
          (2, 3, 1.),
          (2, 4, (-1.)),
          (3, 4, (-6.)),
        ],
      )
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 3), (2, 4), (3, 1), (4, 2)])
    );
  });
});
describe("Blossoms", () => {
  describe("create S-blossom and use it for augmentation.", () => {
    test("S-blossom A", () =>
      Match.Int.make([(1, 2, 8.), (1, 3, 9.), (2, 3, 10.), (3, 4, 7.)])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 2), (2, 1), (3, 4), (4, 3)])
    );
    test("S-blossom B", () =>
      Match.Int.make([
        (1, 2, 8.),
        (1, 3, 9.),
        (2, 3, 10.),
        (3, 4, 7.),
        (1, 6, 5.),
        (4, 5, 6.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 6), (2, 3), (3, 2), (4, 5), (5, 4), (6, 1)])
    );
  });
  describe("Create S-blossom, relabel as T-blossom, use for augmentation.", () => {
    test("S-blossom, relabel as T-blossom: A", () =>
      Match.Int.make([
        (1, 2, 9.),
        (1, 3, 8.),
        (2, 3, 10.),
        (1, 4, 5.),
        (4, 5, 4.),
        (1, 6, 3.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 6), (2, 3), (3, 2), (4, 5), (5, 4), (6, 1)])
    );
    test("S-blossom, relabel as T-blossom: B", () =>
      Match.Int.make([
        (1, 2, 9.),
        (1, 3, 8.),
        (2, 3, 10.),
        (1, 4, 5.),
        (4, 5, 3.),
        (1, 6, 4.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 6), (2, 3), (3, 2), (4, 5), (5, 4), (6, 1)])
    );
    test("S-blossom, relabel as T-blossom: C", () =>
      Match.Int.make([
        (1, 2, 9.),
        (1, 3, 8.),
        (2, 3, 10.),
        (1, 4, 5.),
        (4, 5, 3.),
        (3, 6, 4.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([(1, 2), (2, 1), (3, 6), (4, 5), (5, 4), (6, 3)])
    );
  });
  test("Create nested S-blossom, use for augmentation.", () =>
    Match.Int.make([
      (1, 2, 9.),
      (1, 3, 9.),
      (2, 3, 10.),
      (2, 4, 8.),
      (3, 5, 8.),
      (4, 5, 10.),
      (5, 6, 6.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(1, 3), (2, 4), (3, 1), (4, 2), (5, 6), (6, 5)])
  );
  test("Create S-blossom, relabel as S, include in nested S-blossom.", () =>
    Match.Int.make([
      (1, 2, 10.),
      (1, 7, 10.),
      (2, 3, 12.),
      (3, 4, 20.),
      (3, 5, 20.),
      (4, 5, 25.),
      (5, 6, 10.),
      (6, 7, 10.),
      (7, 8, 8.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 2),
         (2, 1),
         (3, 4),
         (4, 3),
         (5, 6),
         (6, 5),
         (7, 8),
         (8, 7),
       ])
  );
  test("Create nested S-blossom, augment, expand recursively.", () =>
    Match.Int.make([
      (1, 2, 8.),
      (1, 3, 8.),
      (2, 3, 10.),
      (2, 4, 12.),
      (3, 5, 12.),
      (4, 5, 14.),
      (4, 6, 12.),
      (5, 7, 12.),
      (6, 7, 14.),
      (7, 8, 12.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 2),
         (2, 1),
         (3, 5),
         (4, 6),
         (5, 3),
         (6, 4),
         (7, 8),
         (8, 7),
       ])
  );
  test("Create S-blossom, relabel as T, expand.", () =>
    Match.Int.make([
      (1, 2, 23.),
      (1, 5, 22.),
      (1, 6, 15.),
      (2, 3, 25.),
      (3, 4, 22.),
      (4, 5, 25.),
      (4, 8, 14.),
      (5, 7, 13.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 6),
         (2, 3),
         (3, 2),
         (4, 8),
         (5, 7),
         (6, 1),
         (7, 5),
         (8, 4),
       ])
  );
  test("Create nested S-blossom, relabel as T, expand.", () =>
    Match.Int.make([
      (1, 2, 19.),
      (1, 3, 20.),
      (1, 8, 8.),
      (2, 3, 25.),
      (2, 4, 18.),
      (3, 5, 18.),
      (4, 5, 13.),
      (4, 7, 7.),
      (5, 6, 7.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 8),
         (2, 3),
         (3, 2),
         (4, 7),
         (5, 6),
         (6, 5),
         (7, 4),
         (8, 1),
       ])
  );
});
describe("Nasty cases", () => {
  test(
    "Create blossom, relabel as T in more than one way, expand, augment.", () =>
    Match.Int.make([
      (1, 2, 45.),
      (1, 5, 45.),
      (2, 3, 50.),
      (3, 4, 45.),
      (4, 5, 50.),
      (1, 6, 30.),
      (3, 9, 35.),
      (4, 8, 35.),
      (5, 7, 26.),
      (9, 10, 5.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 6),
         (2, 3),
         (3, 2),
         (4, 8),
         (5, 7),
         (6, 1),
         (7, 5),
         (8, 4),
         (9, 10),
         (10, 9),
       ])
  );
  test("Again, but slightly different.", () =>
    Match.Int.make([
      (1, 2, 45.),
      (1, 5, 45.),
      (2, 3, 50.),
      (3, 4, 45.),
      (4, 5, 50.),
      (1, 6, 30.),
      (3, 9, 35.),
      (4, 8, 26.),
      (5, 7, 40.),
      (9, 10, 5.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 6),
         (2, 3),
         (3, 2),
         (4, 8),
         (5, 7),
         (6, 1),
         (7, 5),
         (8, 4),
         (9, 10),
         (10, 9),
       ])
  );
  test(
    "Create blossom, relabel as T, expand such that a new least-slack "
    ++ "S-to-free edge is produced, augment.",
    () =>
    Match.Int.make([
      (1, 2, 45.),
      (1, 5, 45.),
      (2, 3, 50.),
      (3, 4, 45.),
      (4, 5, 50.),
      (1, 6, 30.),
      (3, 9, 35.),
      (4, 8, 28.),
      (5, 7, 26.),
      (9, 10, 5.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 6),
         (2, 3),
         (3, 2),
         (4, 8),
         (5, 7),
         (6, 1),
         (7, 5),
         (8, 4),
         (9, 10),
         (10, 9),
       ])
  );
  test(
    "Create nested blossom, relabel as T in more than one way, expand outer "
    ++ "blossom such that inner blossom ends up on an augmenting path.",
    () =>
    Match.Int.make([
      (1, 2, 45.),
      (1, 7, 45.),
      (2, 3, 50.),
      (3, 4, 45.),
      (4, 5, 95.),
      (4, 6, 94.),
      (5, 6, 94.),
      (6, 7, 50.),
      (1, 8, 30.),
      (3, 11, 35.),
      (5, 9, 36.),
      (7, 10, 26.),
      (11, 12, 5.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 8),
         (2, 3),
         (3, 2),
         (4, 6),
         (5, 9),
         (6, 4),
         (7, 10),
         (8, 1),
         (9, 5),
         (10, 7),
         (11, 12),
         (12, 11),
       ])
  );
  describe("Create nested S-blossom, relabel as S, expand recursively.", () => {
    test("Create nested S-blossom, relabel as S, expand recursively.", () =>
      Match.Int.make([
        (1, 2, 40.),
        (1, 3, 40.),
        (2, 3, 60.),
        (2, 4, 55.),
        (3, 5, 55.),
        (4, 5, 50.),
        (1, 8, 15.),
        (5, 7, 30.),
        (7, 6, 10.),
        (8, 10, 10.),
        (4, 9, 30.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([
           (1, 2),
           (2, 1),
           (3, 5),
           (4, 9),
           (5, 3),
           (6, 7),
           (7, 6),
           (8, 10),
           (9, 4),
           (10, 8),
         ])
    );
    test("Again, but slightly different. (A)", () =>
      Match.Int.make([
        (1, 2, 40.),
        (1, 3, 40.),
        (2, 3, 60.),
        (2, 4, 55.),
        (3, 5, 55.),
        (4, 5, 50.),
        (1, 8, 15.),
        (5, 7, 30.),
        (7, 6, 10.),
        (8, 10, 10.),
        (4, 9, 30.),
        (11, 10, 100.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([
           (1, 8),
           (2, 3),
           (3, 2),
           (4, 5),
           (5, 4),
           (6, 7),
           (7, 6),
           (8, 1),
           (10, 11),
           (11, 10),
         ])
    );
    test("Again, but slightly different. (B)", () =>
      Match.Int.make([
        (1, 2, 40.),
        (1, 3, 40.),
        (2, 3, 60.),
        (2, 4, 55.),
        (3, 5, 55.),
        (4, 5, 50.),
        (1, 8, 15.),
        (5, 7, 30.),
        (7, 6, 10.),
        (8, 10, 10.),
        (4, 9, 30.),
        (3, 6, 36.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([
           (1, 2),
           (2, 1),
           (3, 6),
           (4, 9),
           (5, 7),
           (6, 3),
           (7, 5),
           (8, 10),
           (9, 4),
           (10, 8),
         ])
    );
  });
  test("Blossom with five children.", () => {
    Match.Int.make([
      (9, 8, 30.),
      (9, 5, 55.),
      (9, 3, 6.),
      (9, 1, 50.),
      (8, 3, 18.),
      (8, 4, 10.),
      (7, 3, 15.),
      (7, 6, 10.),
      (5, 3, 40.),
      (5, 2, 60.),
      (3, 2, 40.),
      (3, 4, 16.),
      (2, 1, 55.),
      (1, 0, 43.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (0, 1),
         (1, 0),
         (2, 5),
         (3, 4),
         (4, 3),
         (5, 2),
         (6, 7),
         (7, 6),
         (8, 9),
         (9, 8),
       ])
  });
});
describe("Large data", () => {
  test("Simple large data", () => {
    Match.Int.make([
      (0, 1, 37.333333333333336),
      (0, 2, 52.),
      (0, 3, 41.33333333333333),
      (0, 4, 12.),
      (0, 5, 12.),
      (0, 6, 56.),
      (0, 8, 40.),
      (0, 9, 40.),
      (0, 10, 37.333333333333336),
      (0, 11, 12.),
      (0, 12, 40.),
      (0, 13, 24.),
      (0, 14, 38.4),
      (0, 15, 42.666666666666664),
      (0, 16, 50.66666666666667),
      (0, 17, 42.4),
      (1, 2, 41.33333333333333),
      (1, 3, 60.),
      (1, 4, 12.),
      (1, 5, 44.),
      (1, 6, 41.33333333333333),
      (1, 7, 42.4),
      (1, 8, 8.),
      (1, 9, 12.),
      (1, 10, 48.),
      (1, 11, 44.),
      (1, 12, 40.),
      (1, 13, 5.333333333333333),
      (1, 14, 10.666666666666666),
      (1, 15, 38.4),
      (1, 16, 37.333333333333336),
      (1, 17, 46.666666666666664),
      (2, 3, 37.333333333333336),
      (2, 4, 8.),
      (2, 5, 40.),
      (2, 6, 56.),
      (2, 7, 10.666666666666666),
      (2, 8, 44.),
      (2, 9, 36.),
      (2, 10, 41.33333333333333),
      (2, 11, 40.),
      (2, 12, 12.),
      (2, 13, 56.),
      (2, 14, 42.4),
      (2, 15, 14.666666666666666),
      (2, 16, 56.),
      (2, 17, 6.4),
      (3, 4, 40.),
      (3, 5, 40.),
      (3, 6, 5.333333333333333),
      (3, 7, 38.4),
      (3, 8, 12.),
      (3, 9, 40.),
      (3, 10, 56.),
      (3, 11, 40.),
      (3, 12, 44.),
      (3, 13, 41.33333333333333),
      (3, 14, 14.666666666666666),
      (3, 15, 42.4),
      (3, 16, 9.333333333333332),
      (3, 17, 42.666666666666664),
      (4, 5, 48.),
      (4, 6, 40.),
      (4, 7, 42.666666666666664),
      (4, 8, 54.66666666666667),
      (4, 9, 37.333333333333336),
      (4, 10, 12.),
      (4, 11, 52.),
      (4, 12, 60.),
      (4, 13, 44.),
      (4, 14, 46.666666666666664),
      (4, 15, 46.666666666666664),
      (4, 16, 44.),
      (4, 17, 42.666666666666664),
      (5, 6, 40.),
      (5, 7, 42.666666666666664),
      (5, 8, 24.),
      (5, 9, 37.333333333333336),
      (5, 10, 12.),
      (5, 11, 56.),
      (5, 12, 24.),
      (5, 13, 44.),
      (5, 14, 46.666666666666664),
      (5, 15, 46.666666666666664),
      (5, 16, 12.),
      (5, 17, 42.666666666666664),
      (6, 7, 42.666666666666664),
      (6, 8, 12.),
      (6, 9, 36.),
      (6, 10, 41.33333333333333),
      (6, 11, 40.),
      (6, 12, 12.),
      (6, 13, 52.),
      (6, 14, 42.4),
      (6, 15, 14.666666666666666),
      (6, 16, 52.),
      (6, 17, 38.4),
      (7, 8, 46.666666666666664),
      (7, 9, 4.571428571428571),
      (7, 10, 42.4),
      (7, 11, 42.666666666666664),
      (7, 12, 46.666666666666664),
      (7, 13, 14.666666666666666),
      (7, 14, 44.),
      (7, 15, 28.),
      (7, 16, 14.666666666666666),
      (7, 17, 40.),
      (8, 9, 41.33333333333333),
      (8, 10, 40.),
      (8, 11, 20.),
      (8, 12, 48.),
      (8, 13, 40.),
      (8, 14, 42.666666666666664),
      (8, 15, 42.666666666666664),
      (8, 16, 40.),
      (8, 17, 46.666666666666664),
      (9, 10, 44.),
      (9, 11, 5.333333333333333),
      (9, 12, 41.33333333333333),
      (9, 13, 40.),
      (9, 14, 42.4),
      (9, 15, 40.57142857142857),
      (9, 16, 40.),
      (9, 17, 6.4),
      (10, 11, 12.),
      (10, 12, 40.),
      (10, 13, 5.333333333333333),
      (10, 14, 42.666666666666664),
      (10, 15, 38.4),
      (10, 16, 37.333333333333336),
      (10, 17, 14.666666666666666),
      (11, 12, 52.),
      (11, 13, 44.),
      (11, 14, 46.666666666666664),
      (11, 15, 46.666666666666664),
      (11, 16, 44.),
      (11, 17, 42.666666666666664),
      (12, 13, 40.),
      (12, 14, 10.666666666666666),
      (12, 15, 42.666666666666664),
      (12, 16, 40.),
      (12, 17, 46.666666666666664),
      (13, 14, 38.4),
      (13, 15, 42.666666666666664),
      (13, 16, 48.),
      (13, 17, 42.4),
      (14, 15, 40.),
      (14, 16, 38.4),
      (14, 17, 28.),
      (15, 16, 10.666666666666666),
      (15, 17, 44.),
      (16, 17, 42.4),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (0, 6),
         (1, 3),
         (2, 16),
         (3, 1),
         (4, 12),
         (5, 11),
         (6, 0),
         (7, 14),
         (8, 17),
         (9, 10),
         (10, 9),
         (11, 5),
         (12, 4),
         (13, 15),
         (14, 7),
         (15, 13),
         (16, 2),
         (17, 8),
       ])
  })
});
describe("Input tests", () => {
  test("Duplicate edges are ignored.", () =>
    Match.Int.make([
      (1, 2, 8.),
      (1, 3, 9.),
      (2, 3, 10.),
      (2, 3, 100.),
      (3, 2, 9000.),
      (3, 1, 9000.),
      (3, 4, 7.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(1, 2), (2, 1), (3, 4), (4, 3)])
  );
  test("Non-sequential and negative integers.", () =>
    Match.Int.make([
      (69, (-69), 40.),
      (69, 420, 40.),
      ((-69), 420, 60.),
      ((-69), (-420), 55.),
      (420, 5, 55.),
      ((-420), 5, 50.),
      (69, 8, 15.),
      (5, 7, 30.),
      (7, 6, 10.),
      (8, 10, 10.),
      ((-420), 9, 30.),
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         ((-420), 9),
         ((-69), 69),
         (5, 420),
         (6, 7),
         (7, 6),
         (8, 10),
         (9, (-420)),
         (10, 8),
         (69, (-69)),
         (420, 5),
       ])
  );
  describe("Reversed vertices", () => {
    test(
      "(Reversed) Create nested blossom, relabel as T in more than one way, "
      ++ "expand outer blossom such that inner blossom ends up on an "
      ++ "augmenting path.",
      () =>
      Match.Int.make([
        ((-1), (-2), 45.),
        ((-1), (-7), 45.),
        ((-2), (-3), 50.),
        ((-3), (-4), 45.),
        ((-4), (-5), 95.),
        ((-4), (-6), 94.),
        ((-5), (-6), 94.),
        ((-6), (-7), 50.),
        ((-1), (-8), 30.),
        ((-3), (-11), 35.),
        ((-5), (-9), 36.),
        ((-7), (-10), 26.),
        ((-11), (-12), 5.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([
           ((-12), (-11)),
           ((-11), (-12)),
           ((-10), (-7)),
           ((-9), (-5)),
           ((-8), (-1)),
           ((-7), (-10)),
           ((-6), (-4)),
           ((-5), (-9)),
           ((-4), (-6)),
           ((-3), (-2)),
           ((-2), (-3)),
           ((-1), (-8)),
         ])
    );
    test(
      "(Reversed) Create nested S-blossom, augment, expand recursively.", () =>
      Match.Int.make([
        (8, 7, 8.),
        (8, 6, 8.),
        (7, 6, 10.),
        (7, 5, 12.),
        (6, 4, 12.),
        (5, 4, 14.),
        (5, 3, 12.),
        (4, 2, 12.),
        (3, 2, 14.),
        (2, 1, 12.),
      ])
      |> Match.toList
      |> sortResult(compare)
      |> expect
      |> toEqual([
           (1, 2),
           (2, 1),
           (3, 5),
           (4, 6),
           (5, 3),
           (6, 4),
           (7, 8),
           (8, 7),
         ])
    );
  });
  test("Vertices with edges on themselves are silently ignored.", () =>
    Match.Int.make([(0, 1, 1.), (1, 1, 9001.)])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([(0, 1), (1, 0)])
  );
  test("String vertices", () =>
    Match.String.make([
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
    ])
    |> Match.toList
    |> sortResult(compare)
    |> expect
    |> toEqual([
         ("Andrew", "Gabriel"),
         ("Gabriel", "Andrew"),
         ("James", "Paul"),
         ("John", "Peter"),
         ("Joseph", "Mary"),
         ("Mary", "Joseph"),
         ("Michael", "Raphael"),
         ("Paul", "James"),
         ("Peter", "John"),
         ("Raphael", "Michael"),
       ])
  );
  describe("Arbitrary type vertices", () => {
    test("Variants (nested S-blossom, relabel as S)", () => {
      module Person = {
        type t =
          | Mary
          | Joseph
          | Matthew
          | Mark
          | Luke
          | John
          | Peter
          | Andrew
          | James
          | Philip;
        let toInt =
          fun
          | Mary => 0
          | Joseph => 1
          | Matthew => 2
          | Mark => 3
          | Luke => 4
          | John => 5
          | Peter => 6
          | Andrew => 7
          | James => 8
          | Philip => 9;
        let cmp = (a, b) => compare(toInt(a), toInt(b));
      };
      /*********************************************************
       *  Andrew ---10--- Philip                  Peter        *
       *    |                                    /     \       *
       *   15                                  30       10     *
       *    |                                  /         \     *
       *   Mary ---40--- Matthew ---55---- Luke         John   *
       *      \          /                  /                  *
       *       40      60                 50                   *
       *        \      /                  /                    *
       *         Joseph ------ 55 ----- Mark ----30---- James  *
       ********************************************************/
      Match.make(
        ~id=(module Belt.Id.MakeComparable(Person)),
        ~cmp=Person.cmp,
        Person.[
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
          (Mark, James, 30.),
        ],
      )
      |> Match.toList
      |> sortResult(Person.cmp)
      |> expect
      |> toEqual(
           Person.[
             (Mary, Joseph),
             (Joseph, Mary),
             (Matthew, Luke),
             (Mark, James),
             (Luke, Matthew),
             (John, Peter),
             (Peter, John),
             (Andrew, Philip),
             (James, Mark),
             (Philip, Andrew),
           ],
         );
      /*********************************************************
       *  Andrew -------- Philip                  Peter        *
       *                                               \       *
       *                                                \      *
       *                                                 \     *
       *   Mary          Matthew --------- Luke         John   *
       *      \                                                *
       *       \                                               *
       *        \                                              *
       *         Joseph                 Mark ---------- James  *
       ********************************************************/
    });
    test("Again, with a different cmp function.", () => {
      module Person = {
        type t =
          | Mary
          | Joseph
          | Matthew
          | Mark
          | Luke
          | John;
        let toString =
          fun
          | Mary => "Mary"
          | Joseph => "Joseph"
          | Matthew => "Matthew"
          | Mark => "Mark"
          | Luke => "Luke"
          | John => "John";
        let cmp = (a, b) => compare(toString(a), toString(b));
      };
      Match.make(
        ~id=(module Belt.Id.MakeComparable(Person)),
        ~cmp=Person.cmp,
        Person.[
          (Mary, Joseph, 9.),
          (Mary, Matthew, 9.),
          (Joseph, Matthew, 10.),
          (Joseph, Mark, 8.),
          (Matthew, Luke, 8.),
          (Mark, Luke, 10.),
          (Luke, John, 6.),
        ],
      )
      |> Match.toList
      |> sortResult(Person.cmp)
      |> expect
      |> toEqual(
           Person.[
             (John, Luke),
             (Joseph, Mark),
             (Luke, John),
             (Mark, Joseph),
             (Mary, Matthew),
             (Matthew, Mary),
           ],
         );
    });
    test("Variant constructors", () => {
      module StringOrInt = {
        type t =
          | String(string)
          | Int(int);
        let cmp = (a, b) =>
          switch (a, b) {
          | (String(a), String(b)) => compare(a, b)
          | (Int(a), Int(b)) => compare(a, b)
          | (String(_), Int(_)) => 1
          | (Int(_), String(_)) => (-1)
          };
      };
      Match.make(
        ~id=(module Belt.Id.MakeComparable(StringOrInt)),
        ~cmp=StringOrInt.cmp,
        StringOrInt.[
          (Int(1), Int(2), 40.),
          (Int(1), Int(3), 40.),
          (Int(2), Int(3), 60.),
          (Int(2), Int(4), 55.),
          (Int(3), Int(5), 55.),
          (Int(4), Int(5), 50.),
          (Int(1), String("c"), 15.),
          (Int(5), String("b"), 30.),
          (String("b"), String("a"), 10.),
          (String("c"), String("e"), 10.),
          (Int(4), String("d"), 30.),
        ],
      )
      |> Match.toList
      |> sortResult(StringOrInt.cmp)
      |> expect
      |> toEqual(
           StringOrInt.[
             (Int(1), Int(2)),
             (Int(2), Int(1)),
             (Int(3), Int(5)),
             (Int(4), String("d")),
             (Int(5), Int(3)),
             (String("a"), String("b")),
             (String("b"), String("a")),
             (String("c"), String("e")),
             (String("d"), Int(4)),
             (String("e"), String("c")),
           ],
         );
    });
  });
});
describe("Output tests", () => {
  let result =
    Match.Int.make([
      (1, 2, 40.),
      (1, 3, 40.),
      (2, 3, 60.),
      (2, 4, 55.),
      (3, 5, 55.),
      (4, 5, 50.),
      (1, 8, 15.),
      (5, 7, 30.),
      (7, 6, 10.),
      (8, 10, 10.),
      (4, 9, 30.),
    ]);
  test("get", () =>
    Match.get(result, 5) |> expect |> toBe(Some(3))
  );
  test("get None", () =>
    Match.get(result, 69) |> expect |> toBe(None)
  );
  test("toList", () =>
    Match.toList(result)
    |> sortResult(compare)
    |> expect
    |> toEqual([
         (1, 2),
         (2, 1),
         (3, 5),
         (4, 9),
         (5, 3),
         (6, 7),
         (7, 6),
         (8, 10),
         (9, 4),
         (10, 8),
       ])
  );
  test("toMap", () =>
    Belt.Map.eq(
      Match.toMap(result),
      Belt.Map.fromArray(
        ~id=(module Match.Int.Cmp),
        [|
          (1, 2),
          (2, 1),
          (3, 5),
          (4, 9),
          (5, 3),
          (6, 7),
          (7, 6),
          (8, 10),
          (9, 4),
          (10, 8),
        |],
      ),
      (==),
    )
    |> expect
    |> toBe(true)
  );
  test("forEach", () => {
    let arr = Array.make(11, -1);
    Match.forEach(result, ~f=(v1, v2) => ignore(arr[v1] = v2));
    expect(arr) |> toEqual([|(-1), 2, 1, 5, 9, 3, 7, 6, 10, 4, 8|]);
  });
  test("isEmpty", () =>
    Match.isEmpty(result) |> expect |> toBe(false)
  );
  test("has", () =>
    Match.has(result, 5) |> expect |> toBe(true)
  );
  test("reduce", () =>
    Match.reduce(result, ~init="", ~f=(acc, v1, v2) => {j|($v1, $v2), $acc|j})
    |> expect
    |> toBe(
         "(10, 8), (9, 4), (8, 10), (7, 6), (6, 7), (5, 3), (4, 9), (3, 5), "
         ++ "(2, 1), (1, 2), ",
       )
  );
});
