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
open Belt;

module JsBlossom = {
  type t = (. array((int, int, float))) => array(int);

  /* Turn a list of lists into a list of arrays for JS */

  /* Functions to convert non-integer data for use by jsBlossom.
   * These may or may not reflect practical real-world use. They're just a
   * quick-and dirty way to make it work. */

  let makeKeys:
    (list(('v, 'v, float)), Belt.Id.comparable('v, 'identity)) =>
    (Map.Int.t('v), Map.t('v, int, 'identity)) =
    (inputArray, id) => {
      let emptyMap = Map.make(~id);
      let emptySet = Set.make(~id);
      let (intMap, vertexMap, _) =
        /* Make a set of unique vertices. */
        List.reduceU(inputArray, emptySet, (. acc, (i, j, _w)) =>
          acc->Set.add(i)->Set.add(j)
        )
        /* Map them to integer indices */
        ->Set.reduceU(
            (Map.Int.empty, emptyMap, 0), (. (intMap, strMap, index), x) =>
            (
              Map.Int.set(intMap, index, x),
              Map.set(strMap, x, index),
              succ(index),
            )
          );
      (intMap, vertexMap);
    };

  let graphToIntGraph:
    (list(('v, 'v, float)), Map.t('v, int, 'identity)) =>
    array((int, int, float)) =
    (inputArray, strMap) =>
      List.reduceU(inputArray, [||], (. acc, (i, j, w)) =>
        Array.concat(
          acc,
          [|(Map.getExn(strMap, i), Map.getExn(strMap, j), w)|],
        )
      );

  let intResultToResult: (array(int), Map.Int.t('v)) => list(('v, 'v)) =
    (inputArray, intMap) =>
      Array.reduceWithIndexU(inputArray, [], (. acc, x, y) =>
        [(Map.Int.getExn(intMap, x), Map.Int.getExn(intMap, y)), ...acc]
      );
};

module BenchmarkJs = {
  type t;
  module Stats = {
    type t = {
      rme: float,
      sample: array(float),
    };
  };
  module Benchmark = {
    type t = {
      name: string,
      hz: float,
      stats: Stats.t,
    };
  };
  module Suite = {
    type t = Js.Dict.t(Benchmark.t);
    [@bs.get] external name: t => string = "name";
    [@bs.get] external length: t => int = "length";
  };
  type event = {
    currentTarget: Suite.t,
    target: Benchmark.t,
  };
  type options = {async: bool};
  [@bs.send] external add: (t, string, unit => unit) => t = "add";
  [@bs.send]
  external on:
    (t, [@bs.string] [ | `cycle | `start | `complete], event => unit) => t =
    "on";
  [@bs.send] external run: (t, options) => unit = "run";
};

let percentDiff = (a, b) => floor((b -. a) /. b *. 100.);

let formatResult = (BenchmarkJs.Benchmark.{name, hz, _}, maxHz) => {
  (percentDiff(hz, maxHz)->Js.String.make ++ "% slower", name);
};

module NodeLogger = NodeLogger;
/* This makes it easy to import in the browser. */
module BrowserLogger = {
  include BrowserLogger;
};

module type Logger = {
  let info: (string, string) => unit;
  let infoWithData2: (string, string, (string, 'a), (string, 'b)) => unit;
  let infoWithData3:
    (string, string, (string, 'a), (string, 'b), (string, 'c)) => unit;
  let infoWithData6:
    (
      string,
      string,
      (string, 'a),
      (string, 'b),
      (string, 'c),
      (string, 'd),
      (string, 'e),
      (string, 'f)
    ) =>
    unit;
};

let make: ((module Logger), BenchmarkJs.t, JsBlossom.t) => unit =
  (logger, suite, jsBlossom) => {
    module Logger = (val logger);
    BenchmarkJs.(
      suite
      ->add("Re-Blossom: Integers", () =>
          List.forEachU(BenchData.Int.data, (. x) => Match.Int.make(x))
        )
      ->add("JS Blossom: Integers", () =>
          List.forEachU(BenchData.Int.data, (. x) =>
            jsBlossom(. List.toArray(x))
          )
        )
      ->add("Re-Blossom: Strings ", () =>
          List.forEachU(BenchData.String.data, (. x) => Match.String.make(x))
        )
      ->add("JS Blossom: Strings ", () => {
          List.forEachU(
            BenchData.String.data,
            (. x) => {
              let (intMap, vertexMap) =
                JsBlossom.makeKeys(x, (module BenchData.String.Cmp));
              let y = JsBlossom.graphToIntGraph(x, vertexMap);
              let mates = jsBlossom(. y);
              JsBlossom.intResultToResult(mates, intMap);
            },
          )
        })
      ->add("Re-Blossom: Variants", () => {
          List.forEachU(BenchData.Person.data, (. x) =>
            Match.make(
              ~id=(module BenchData.Person.Cmp),
              ~cmp=BenchData.Person.cmp,
              x,
            )
          )
        })
      ->add("JS Blossom: Variants", () => {
          List.forEachU(
            BenchData.Person.data,
            (. x) => {
              let (intMap, vertexMap) =
                JsBlossom.makeKeys(x, (module BenchData.Person.Cmp));
              let y = JsBlossom.graphToIntGraph(x, vertexMap);
              let mates = jsBlossom(. y);
              JsBlossom.intResultToResult(mates, intMap);
            },
          )
        })
      ->on(`start, ({currentTarget, _}) =>
          Logger.infoWithData2(
            __MODULE__,
            "Beginning benchmark",
            ("name", currentTarget->Suite.name),
            ("tests", currentTarget->Suite.length),
          )
        )
      ->on(`cycle, ({target, _}) =>
          Logger.info(__MODULE__, target->Js.String.make)
        )
      ->on(
          `complete,
          ({currentTarget, _}) => {
            open Benchmark;
            let results =
              currentTarget
              ->Suite.length
              ->List.makeBy(x => Js.String.make(x))
              ->List.keepMap(Js.Dict.get(currentTarget))
              ->List.sort((a, b) => compare(b.hz, a.hz));
            switch (results) {
            | [] => Logger.info(__MODULE__, "No results? :(")
            | [first, second, third, fourth, fifth, sixth] =>
              Logger.infoWithData6(
                __MODULE__,
                "Percenage comparison",
                ("   Fastest", first.name),
                formatResult(second, first.hz),
                formatResult(third, first.hz),
                formatResult(fourth, first.hz),
                formatResult(fifth, first.hz),
                formatResult(sixth, first.hz),
              )
            | [{name, hz: maxHz, _}, ...results] =>
              Js.log("  Fastest  : " ++ name);
              List.forEach(results, result => {
                formatResult(result, maxHz)->Js.log
              });
            };
            Logger.info(__MODULE__, "Done");
          },
        )
      ->run({async: true})
    );
  };
let default = make;
