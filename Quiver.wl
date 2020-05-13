(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Quiver`", {"QuiverGaugeTheory`Main`"}]


Unprotect["QuiverGaugeTheory`Quiver`*"];
ClearAll["QuiverGaugeTheory`Quiver`*"];


GraphEdgeQ::usage = "";


QuiverFields::usage = "";


FindQuiverPaths::usage = "";


QuiverPathToFields::usage = "";


QuiverLoops::usage = "";


QuiverFromPotential::usage = "";


QuiverGraph::usage = "";


QuiverIncidenceMatrix::usage = "";


Begin["`Private`"]


GraphOpts = Sequence[
   PlotTheme -> "ClassicDiagram",
   VertexLabelStyle -> Directive[Bold, 14],
   EdgeShapeFunction -> GraphElementData["Arrow"]
];


SyntaxInformation[GraphEdgeQ] = {"ArgumentsPattern" -> {_}};

GraphEdgeQ = MatchQ[{ (DirectedEdge[__]|UndirectedEdge[__]) .. }];


SyntaxInformation[QuiverFromPotential] = {"ArgumentsPattern" -> {_}};

QuiverFromPotential[W_] := 
  ReplaceAll[{Subscript[X, _] -> DirectedEdge}]@FieldsInPotential[W];


SyntaxInformation[QuiverFields] = {"ArgumentsPattern" -> {_}};

QuiverFields[edges_?GraphEdgeQ] := 
  KeyValueMap[Table[Subscript[X, i] @@ #1, {i, Range[#2]}] &, Counts@edges] // Flatten;


SyntaxInformation[FindQuiverPaths] = {"ArgumentsPattern" -> {_, _, _, _}};

FindQuiverPaths[edges_?GraphEdgeQ, i_, j_, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] := 
  Join @@ (FindQuiverPaths[edges, i, j, #] & /@ SortBy[First]@degspec);
FindQuiverPaths[edges_?GraphEdgeQ, i_, j_, deg_] := 
  FindPath[edges, i, j, deg, All] // Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &];


SyntaxInformation[QuiverLoops] = {"ArgumentsPattern" -> {_, _}};

QuiverLoops[edges_?GraphEdgeQ, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] := 
  Join @@ (QuiverLoops[edges, #] & /@ SortBy[First]@degspec);
QuiverLoops[edges_?GraphEdgeQ, deg_] := 
  FindCycle[edges, deg, All];


SyntaxInformation[QuiverPathToFields] = {"ArgumentsPattern" -> {_, _.}};

QuiverPathToFields[edges_?GraphEdgeQ] := 
  QuiverPathToFields[#, edges] &;
QuiverPathToFields[paths: {__?GraphEdgeQ}, edges_?GraphEdgeQ] :=
  QuiverPathToFields[#, edges] & /@ paths;
QuiverPathToFields[path_?GraphEdgeQ, edges_?GraphEdgeQ] := 
  path/.KeyValueMap[#1 -> Table[Subscript[X, i]@@#1, {i, Range@#2}] &, Counts@edges] //
  Outer[Times, Sequence@@#1] & // Flatten;


SyntaxInformation[QuiverGraph] = {"ArgumentsPattern" -> {_, _., OptionsPattern[]}};

QuiverGraph[W_?PotentialQ, opts:OptionsPattern[Graph] ] := 
  QuiverGraph[QuiverFromPotential@W, opts];
QuiverGraph[vertex:{__Integer}, W_?PotentialQ, opts:OptionsPattern[Graph] ] :=
  QuiverGraph[vertex, QuiverFromPotential@W, opts];
QuiverGraph[edges_?GraphEdgeQ, opts:OptionsPattern[Graph] ] := 
  QuiverGraph[Sort@DeleteDuplicates@Flatten[List@@@edges], edges, opts];
QuiverGraph[vertex:{__Integer}, edges_?GraphEdgeQ, opts:OptionsPattern[Graph] ] := 
  Graph[vertex, edges, opts, GraphOpts, 
    VertexCoordinates -> ReIm@Exp[2 Pi I Range[0, Length@vertex - 1]/Length@vertex
        + I Pi Switch[Length@vertex, 3, 1/2, 4, 1/4, 5, 1/10, 7, 3/14, _, 0] ]
  ];


SyntaxInformation[QuiverIncidenceMatrix] = {"ArgumentsPattern" -> {_}};

QuiverIncidenceMatrix[W_] := 
  QuiverIncidenceMatrix[QuiverFromPotential@W];
QuiverIncidenceMatrix[edges_?GraphEdgeQ] :=
  TableForm[
    Transpose@Normal@IncidenceMatrix[edges], 
    TableHeadings -> {
      QuiverFields@edges, 
      Thread@Subscript[U[1], Range@Length@QuiverFields@edges]
    }
  ];


With[{syms = Names["QuiverGaugeTheory`Quiver`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
]

End[]

EndPackage[]
