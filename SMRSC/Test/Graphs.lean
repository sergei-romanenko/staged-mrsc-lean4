--
-- SMRSC.Test.Graphs
--

import SMRSC.Util
import SMRSC.Graphs

def ibad (c:Nat) : Bool
  := c >= 100

def g_back : Graph Nat :=
  .back 1

def g_forth : Graph Nat :=
  .forth 1 [.back 1]

def g1 : Graph Nat :=
  .forth 1 [
    .back 1,
    .forth 2 [
      .back 1,
      .back 2]]

def g_bad_forth : Graph Nat :=
  .forth 1 [
    .back 1,
    .forth 102 [
      .back 3,
      .back 4]]

def g_bad_back : Graph Nat :=
  .forth 1 [
    .back 1,
    .forth 2 [
      .back 3,
      .back 104]]

def l2 : LazyGraph Nat :=
  .build 1 [
    [.build 2 [[.stop 1, .stop 2]] ],
    [.build 3 [[.stop 3, .stop 1]] ]]

def gs2 : List (Graph Nat) := [
  .forth 1 [.forth 2 [.back 1, .back 2]],
  .forth 1 [.forth 3 [.back 3, .back 1]]]

def l_empty : LazyGraph Nat :=
  .build 1 [
    [.stop 2],
    [.build 3 [
      [.stop 4, .empty]]]]

def l_bad_build : LazyGraph Nat :=
  .build 1 [[
    .stop 1,
    .build 102 [[
      .stop 3, .stop 4]]]]

def l_bad_stop : LazyGraph Nat :=
  .build 1 [[
    .stop 1,
    .build 2 [[
      .stop 3,
      .stop 104]]]]

def l3 : LazyGraph Nat :=
  .build 1 [
    [.build 2 [[
      .stop 1, .stop 2]]],
    [.build 3 [[
      .stop 4]]]]

#guard reprStr g_back == "Graph.back 1"
#guard reprStr g_forth == "Graph.forth 1 [Graph.back 1]"

#guard toString g_back == "back 1"
#guard toString  g_forth == "forth 1 [back 1]"
#guard toString  g1 == "forth 1 [back 1, forth 2 [back 1, back 2]]"

#guard reprStr l2 == "\
LazyGraph.build
  1
  [[LazyGraph.build 2 [[LazyGraph.stop 1, LazyGraph.stop 2]]],
   [LazyGraph.build 3 [[LazyGraph.stop 3, LazyGraph.stop 1]]]]"

#guard reprStr l_empty == "\
LazyGraph.build 1 [[LazyGraph.stop 2], [LazyGraph.build 3 [[LazyGraph.stop 4, LazyGraph.empty]]]]"

#guard Graph.back 1 == .back 1
#guard Graph.back 1 != .back 2
#guard Graph.forth 1 [.back 1] == .forth 1 [.back 1]
#guard Graph.forth 1 [.back 1] != .forth 2 [.back 1]
#guard Graph.forth 1 [.back 1] != .forth 1 [.back 2]

#guard toString l2 ==
  "build 1 [[build 2 [[stop 1, stop 2]]], [build 3 [[stop 3, stop 1]]]]"
#guard toString l_empty ==
  "build 1 [[stop 2], [build 3 [[stop 4, empty]]]]"

#guard LazyGraph.empty (α := Nat) == .empty
#guard LazyGraph.stop 1 == .stop 1
#guard LazyGraph.stop 1 != .stop 2
#guard LazyGraph.build 1 [[.stop 1]] == .build 1 [[.stop 1]]
#guard LazyGraph.build 1 [[.stop 1]] != .build 2 [[.stop 1]]
#guard LazyGraph.build 1 [[.stop 1]] != .build 1 [[.stop 2]]

#guard unroll (LazyGraph.empty (α := Nat)) == []
#guard unroll (LazyGraph.stop 100) == [.back 100]
#guard unroll l2 == gs2

#guard !bad_graph ibad g1
#guard bad_graph ibad g_bad_forth
#guard bad_graph ibad g_bad_back

#guard cl_empty l_empty == .build 1 [[.stop 2]]

#guard cl_bad_conf ibad l_bad_build ==
    .build 1 [[.stop 1, .empty]]
#guard cl_bad_conf ibad l_bad_stop ==
    .build 1 [[.stop 1, .build 2 [[.stop 3, .empty]]]]

#guard cl_empty_and_bad ibad l_bad_build == .empty
#guard cl_empty_and_bad ibad l_bad_stop == .empty

#guard graph_size g1 == 5

#guard cl_min_size l3 ==
    (5, .build 1 [[.build 3 [[.stop 4]]]])

#guard
  let min_l := (cl_min_size l3).snd
  let min_g := unroll min_l
  min_g == [.forth 1 [.forth 3 [.back 4]]]

#guard cartesian (α := Graph Nat) [] == [[]]
#guard cartesian (α := Graph Nat) [[]] == []
#guard cartesian (α := Graph Nat) [[.back 1, .back 2]] == [[.back 1], [.back 2]]
#guard cartesian (α := Graph Nat) [[.back 1], []] == []
#guard cartesian (α := Graph Nat) [[.back 1, .back 2], [.back 10, .back 20]] ==
    [
      [.back 1, .back 10], [.back 1, .back 20],
      [.back 2, .back 10], [.back 2, .back 20]
    ]

def pp_graph : Graph Nat :=
  .forth 100 [
    .forth 101 [.back 100],
    .forth 102 [.forth 101 [.back 100]]]

def pp_string : String := "\
|__100
  |
  |__101
    |
    |__100*
  |
  |__102
    |
    |__101
      |
      |__100*\
"

#guard graph_pp pp_graph == pp_string
