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
  let data_int = List.map(BenchData.IntData.data, List.toArray);
  let data_str = List.map(BenchData.StringData.data, List.toArray);

  /* Functions to convert non-integer data for use by jsBlossom.
   * These may or may not reflect practical real-world use. They're just a
   * quick-and dirty way to make it work. */

  let makeStrToIntKey:
    array((string, string, float)) =>
    (Map.Int.t(string), Map.String.t(int)) =
    inputArray => {
      let (intMap, strMap, _) =
        /* Make a set of unique vertices. */
        Array.reduceU(inputArray, Set.String.empty, (. acc, (i, j, _w)) =>
          acc->Set.String.add(i)->Set.String.add(j)
        )
        /* Map them to integer indices */
        ->Set.String.reduceU(
            (Map.Int.empty, Map.String.empty, 0),
            (. (intMap, strMap, index), x) =>
            (
              Map.Int.set(intMap, index, x),
              Map.String.set(strMap, x, index),
              succ(index),
            )
          );
      (intMap, strMap);
    };

  let strGraphToIntGraph:
    (array((string, string, float)), Map.String.t(int)) =>
    array((int, int, float)) =
    (inputArray, strMap) =>
      Array.reduceU(inputArray, [||], (. acc, (i, j, w)) =>
        Array.concat(
          acc,
          [|
            (Map.String.getExn(strMap, i), Map.String.getExn(strMap, j), w),
          |],
        )
      );

  let intResultToStrResult:
    (array(int), Map.Int.t(string)) => list((string, string)) =
    (inputArray, intMap) =>
      Array.reduceWithIndexU(inputArray, [], (. acc, x, y) =>
        [(Map.Int.getExn(intMap, x), Map.Int.getExn(intMap, y)), ...acc]
      );
};

module BenchmarkJs = {
  type t;
  module CurrentTarget = {
    type benchmark = {
      name: string,
      hz: float,
    };
    type t = Js.Dict.t(benchmark);
    [@bs.get] external name: t => string = "name";
  };
  type eventTarget;
  type event = {
    currentTarget: CurrentTarget.t,
    target: eventTarget,
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

let make: (BenchmarkJs.t, JsBlossom.t) => unit =
  (suite, jsBlossom) => {
    BenchmarkJs.(
      suite
      ->add("Re-Blossom: Integers", () =>
          List.forEachU(BenchData.IntData.data, (. x) => Match.Int.make(x))
        )
      ->add("JS Blossom: Integers", () =>
          List.forEachU(JsBlossom.data_int, jsBlossom)
        )
      ->add("Re-Blossom: Strings ", () =>
          List.forEachU(BenchData.StringData.data, (. x) =>
            Match.String.make(x)
          )
        )
      ->add("JS Blossom: Strings ", () => {
          List.forEachU(
            JsBlossom.data_str,
            (. x) => {
              let (intMap, strMap) = JsBlossom.makeStrToIntKey(x);
              let y = JsBlossom.strGraphToIntGraph(x, strMap);
              let mates = jsBlossom(. y);
              JsBlossom.intResultToStrResult(mates, intMap);
            },
          )
        })
      ->on(
          `start,
          ({currentTarget, _}) => {
            Js.log(currentTarget->CurrentTarget.name);
            Js.log("**Beginning benchmarks. Higher ops/sec is better.**");
          },
        )
      ->on(`cycle, ({target, _}) => target->Js.String.make->Js.log)
      ->on(
          `complete,
          ({currentTarget, _}) => {
            open CurrentTarget;
            Js.log("**Percentage comparison**");
            let results =
              List.keepMap(["0", "1", "2", "3"], Js.Dict.get(currentTarget))
              ->List.sort((a, b) => compare(b.hz, a.hz));
            switch (results) {
            | [] => Js.log("No results? :(")
            | [{name, hz: maxHz}, ...results] =>
              Js.log("  Fastest  : " ++ name);
              List.forEach(
                results,
                ({name, hz}) => {
                  let percent = percentDiff(hz, maxHz)->Js.String.make;
                  let leftPad =
                    switch (Js.String.length(percent)) {
                    | 1 => " "
                    | _ => ""
                    };
                  Js.log(leftPad ++ percent ++ "% slower : " ++ name);
                },
              );
            };
            Js.log("**Done.**");
          },
        )
      ->run({async: true})
    );
  };
let default = make;
