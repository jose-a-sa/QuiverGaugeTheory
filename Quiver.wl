(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Quiver`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Core`"
}]


QuiverFields::usage = "";
FindQuiverPaths::usage = "";
FindQuiverPathsWithCycles::usage = "";
QuiverPathToFields::usage = "";
QuiverCycles::usage = "";
QuiverFromFields::usage = "";
GaugeInvariantMesons::usage = "";
QuiverGraph::usage = "";
QuiverIncidenceMatrix::usage = "";


$QuiverRotationByDegree = {3 -> Pi/2, 4 -> Pi/4, 5 -> Pi/10, 7 -> 3 Pi/14};
$QuiverVertexGroupingSpread = Pi/20;


Begin["`Private`"]


SyntaxInformation[QuiverFromFields] = {"ArgumentsPattern" -> {_}};

QuiverFromFields[W_] := 
  ReplaceAll[{Subscript[X, _] -> DirectedEdge}]@Fields[W];


SyntaxInformation[QuiverFields] = {"ArgumentsPattern" -> {_}};

QuiverFields[edges_?EdgeListQ] := 
  Flatte@KeyValueMap[Table[Subscript[X, i] @@ #1, {i, Range[#2]}] &, Counts@edges] // Flatten;


SyntaxInformation[FindQuiverPaths] = {"ArgumentsPattern" -> {_, _, _, _}};

FindQuiverPaths[edges_?EdgeListQ, i_, j_, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] :=
  Switch[edges,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, Join @@ (FindQuiverPaths[edges, i, j, #, All] & /@ SortBy[First]@degspec);
  ]
FindQuiverPaths[edges_?EdgeListQ, i_, j_, deg_] :=
  Switch[edges,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, FindPath[edges, i, j, deg, All] // 
      Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &]
  ]


SyntaxInformation[FindQuiverPathsWithCycles] = {"ArgumentsPattern" -> {_, _, _, _}};

FindQuiverPathsWithCycles[edges_?EdgeListQ, i_, j_, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] :=
  Switch[edges,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, Join @@ (FindPathWithCycles[edges, i, j, #] & /@ SortBy[First]@degspec);
  ]
FindQuiverPathsWithCycles[edges_?EdgeListQ, i_, j_, deg_] :=
  Switch[edges,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, FindPathWithCycles[edges, i, j, deg] // 
      Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &]
  ]


SyntaxInformation[QuiverLoops] = {"ArgumentsPattern" -> {_, _}};
QuiverCycles[edges_?EdgeListQ, 
    kspec : {({_Integer, _Integer | Infinity} | {_Integer}) ..}] := 
  Join @@ (QuiverCycles[edges, #] & /@ SortBy[First]@kspec);
QuiverCycles[edges_?EdgeListQ, k_Integer] := 
  QuiverCycles[edges, {1, k}]
QuiverCycles[edges_?EdgeListQ, Infinity] := 
  QuiverCycles[edges, {1, \[Infinity]}]
QuiverCycles[edges_?EdgeListQ, {k_Integer}] := 
  QuiverCycles[edges, {k, k}]
QuiverCycles[edges_?EdgeListQ, {kmin : _Integer, kmax : _Integer | Infinity}] :=
  Module[{cyc2up, cyc1},
    cyc2up = FindCycle[edges, {kmin, kmax}, All];
    cyc1 = Cases[edges, (DirectedEdge | UndirectedEdge)[i_, i_, ___] ] //
      DeleteDuplicates // Map[List];
    If[kmin <= 1 <= kmax, Join[cyc1, cyc2up], cyc2up]
  ]


SyntaxInformation[QuiverPathToFields] = {"ArgumentsPattern" -> {_, _.}};

QuiverPathToFields[edges_?EdgeListQ] := 
  QuiverPathToFields[#, edges] &;
QuiverPathToFields[paths: {__?EdgeListQ}, edges_?EdgeListQ] :=
  QuiverPathToFields[#, edges] & /@ paths;
QuiverPathToFields[path_?EdgeListQ, edges_?EdgeListQ] := 
  path/.KeyValueMap[#1 -> Table[Subscript[X, i]@@#1, {i, #2}] &, Counts@edges] //
    Outer[Times, Sequence@@#1] & // Flatten;


SyntaxInformation[GaugeInvariantMesons] = {"ArgumentsPattern" -> {_, _}};

GaugeInvariantMesons[edges_?EdgeListQ, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] := 
  Flatten@QuiverPathToFields[QuiverCycles[edges, degspec], edges];
GaugeInvariantMesons[edges_?EdgeListQ, deg_] := 
  Flatten@QuiverPathToFields[QuiverCycles[edges, deg], edges];



parseVertexPositioning[v : {(_Integer | {__Integer}) ..}] :=
  Module[{spread, shifts, parsedV, polyV, nV = Length@v},
    spread = $QuiverVertexGroupingSpread;
    shifts = SparseArray[$QuiverRotationByDegree, 100];
    parsedV = Map[Flatten@*List, v];
    polyV = Thread[ parsedV -> Exp[2 Pi I Range[0,nV-1]/nV + I shifts[[nV]] ] ];
    (Thread[#1 -> ReIm[#2 Exp[ I spread Range[-Length@#1 + 1, Length@#1 - 1, 2]/2] ]
      ] &) @@@ polyV // Flatten
  ];


parseArrowheads[edges_, s: (_?NumericQ): 0.04, p: (_?NumericQ | {_?NumericQ,_?NumericQ}): 0.8] :=
  Module[{shapeF, parsePos, f, b},
    {f, b} = If[MatchQ[p, {_, _}], p, {p, 1 - p}];
    parsePos[l_] := (# + {0, First@MaximalBy[
      {-Min[MinimalBy[l,Last],0], -Max[MaximalBy[l,Last] - 1, 0]},
        Abs]} &) /@ l;
    shapeF[edge_, ah_] := edge -> ({ah, Arrow[#]} &);
    GroupBy[edges, Sort -> (Signature[#] &)] //
      Map[{Count[-1]@#, Count[+1]@#} &] //
      ApplyTo[Arrowheads[Join @@ parsePos /@ {
        Table[{-s,b+(2*k-#1+1)*2*s/3}, {k,0,#1-1}],
        Table[{+s,f+(2*k-#2+1)*2*s/3}, {k,0,#2-1}]
      }] &, {1}] //
    KeyValueMap[shapeF]
   ];


SyntaxInformation[QuiverGraph] = {
  "ArgumentsPattern" -> {_, ___},
  "OptionsName" -> {
    "MultiplicityAsEdges", 
    "ArrowsPosition",
    "ArrowSize"}
  };


Options[QuiverGraph] = {
  VertexSize -> {"Scaled", 0.04},
  VertexStyle -> Directive[ EdgeForm[{Black}], FaceForm[{Hue[0.15, 0.2, 1]}] ],
  VertexLabels -> Placed[Automatic, {0.52, 0.48}],
  VertexLabelStyle -> Directive[ Bold, FontSize -> Scaled[0.04] ],
  EdgeStyle -> Directive[ Opacity[1], Hue[0, 1, 0.5] ],
  "MultiplicityAsEdges" -> False,
  "ArrowSize" -> 0.04,
  "ArrowsPosition" -> {0.8, 0.16}
};

QuiverGraph[W_?PotentialQ, opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[Automatic, QuiverFromFields@W, opts];
QuiverGraph[Automatic, edges_?EdgeListQ, opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[Sort@DeleteDuplicates@Flatten[List@@@edges], edges, opts];
QuiverGraph[Automatic, W_?PotentialQ, opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[Automatic, QuiverFromFields@W, opts];
QuiverGraph[vertex: {(_Integer|{__Integer})..}, W_?PotentialQ, 
  opts: OptionsPattern[{QuiverGraph, Graph}] ] :=
    QuiverGraph[vertex, QuiverFromFields@W, opts];
QuiverGraph[vertex: {(_Integer | {__Integer}) ..}, edges_?EdgeListQ, 
  opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
    Graph[
      Flatten@vertex,
      If[OptionValue["MultiplicityAsEdges"],
        Identity, Map[First]@*parseArrowheads]@edges,
      Sequence @@ FilterRules[{opts}, Except[
        Union[Options@QuiverGraph, {EdgeShapeFunction}], 
        Options@Graph]
      ],
      VertexSize -> OptionValue["VertexSize"],
      VertexStyle -> OptionValue["VertexStyle"],
      VertexLabels -> OptionValue["VertexLabels"],
      VertexLabelStyle -> OptionValue["VertexLabelStyle"],
      VertexCoordinates -> parseVertexPositioning[vertex],
      EdgeStyle -> OptionValue["EdgeStyle"],
      EdgeShapeFunction -> If[
        OptionValue["MultiplicityAsEdges"],
        GraphElementData[{"FilledArrow", "ArrowSize" -> OptionValue["ArrowSize"]}],
        parseArrowheads[edges, OptionValue["ArrowSize"], OptionValue["ArrowsPosition"] ]
      ]
    ];


SyntaxInformation[QuiverIncidenceMatrix] = {"ArgumentsPattern" -> {_}};

QuiverIncidenceMatrix[W_?PotentialQ] := 
  QuiverIncidenceMatrix[QuiverFromFields@W];
QuiverIncidenceMatrix[edges_?EdgeListQ] :=
  Graph[Sort@DeleteDuplicates@Flatten[List@@@edges], edges] //
    IncidenceMatrix // Normal[-#] &;


End[]

EndPackage[]
