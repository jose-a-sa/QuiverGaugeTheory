(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Quiver`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`"
}]


QuiverEdgesQ::usage = "";
FieldsToEdges::usage = "";
FieldsToTaggedEdges::usage = "";
QuiverFromFields::usage = "";
QuiverCycles::usage = "";
QuiverPathToFields::usage = "";
GaugeInvariantMesons::usage = "";
QuiverIncidenceMatrix::usage = "";
MesonQ::usage = "";
OrderedMesonQ::usage = "";
GaugeInvariantQ::usage = "";
Mesons::usage = "";
ReorderLoopEdges::usage = "";
NonAbelianizeMesons::usage = "";
FindQuiverPaths::usage = "";
QuiverGraph::usage = "";


$QuiverRotationByDegree = {3 -> Pi/2, 4 -> Pi/4, 5 -> Pi/10, 7 -> 3 Pi/14};
$QuiverVertexGroupingSpread = Pi/20;


Begin["`Private`"]


SyntaxInformation[QuiverEdgesQ] = {"ArgumentsPattern" -> {_}};
QuiverEdgesQ[KeyValuePattern[DirectedEdge[__] -> _] ] := True;
QuiverEdgesQ[_] := False


SyntaxInformation[FieldsToEdges] = {"ArgumentsPattern" -> {_}};
FieldsToEdges[expr_] :=
  ReplaceAll[{Subscript[X, _] -> DirectedEdge}]@expr;


SyntaxInformation[FieldsToTaggedEdges] = {"ArgumentsPattern" -> {_}};
FieldsToTaggedEdges[expr_] :=
  ReplaceAll[{Subscript[X, k_][i_,j_] :> DirectedEdge[i, j, k]}]@expr;


SyntaxInformation[QuiverFromFields] = {"ArgumentsPattern" -> {_}};
QuiverFromFields[expr_] := 
  KeySort@GroupBy[Fields[expr], Apply[DirectedEdge] ];


SyntaxInformation[QuiverCycles] = {"ArgumentsPattern" -> {_, _}};
QuiverCycles[edges: ( _?QuiverEdgesQ | _?EdgeListQ ), 
    kspec : {({_Integer, _Integer|Infinity} | {_Integer}) ..}] := 
  Join @@ (QuiverCycles[edges, #] & /@ SortBy[First]@kspec);
QuiverCycles[edges: ( _?QuiverEdgesQ | _?EdgeListQ ), k_Integer] := 
  QuiverCycles[edges, {1, k}]
QuiverCycles[edges: ( _?QuiverEdgesQ | _?EdgeListQ ), Infinity] := 
  QuiverCycles[edges, {1, \[Infinity]}]
QuiverCycles[edges: ( _?QuiverEdgesQ | _?EdgeListQ ), {k_Integer}] := 
  QuiverCycles[edges, {k, k}]
QuiverCycles[edges_?QuiverEdgesQ, {kmin_Integer, kmax: _Integer|Infinity}] :=
  QuiverCycles[KeysByValueLength@edges, {kmin, kmax}];
QuiverCycles[edges_?EdgeListQ, {kmin_Integer, kmax: _Integer|Infinity}] :=
  Module[{cyc2up, cyc1},
    cyc2up = FindCycle[edges, {kmin, kmax}, All];
    cyc1 = Cases[edges, (DirectedEdge | UndirectedEdge)[i_, i_, ___] ] //
      DeleteDuplicates // Map[List];
    If[kmin <= 1 <= kmax, Join[cyc1, cyc2up], cyc2up]
  ]


SyntaxInformation[QuiverPathToFields] = {"ArgumentsPattern" -> {_, _.}};
QuiverPathToFields[edges: (_?QuiverEdgesQ | _?EdgeListQ)][paths: {__?EdgeListQ}|_?EdgeListQ] := 
  QuiverPathToFields[paths, edges];
QuiverPathToFields[paths: {__?EdgeListQ}, edges: (_?QuiverEdgesQ | _?EdgeListQ)] :=
  QuiverPathToFields[#, edges] & /@ paths;
QuiverPathToFields[path_?EdgeListQ, edges_?EdgeListQ] := 
  QuiverPathToFields[path, 
    KeyValueMap[#1 -> Table[Subscript[X, i]@@#1, {i, #2}] &, Counts@edges]
  ];
QuiverPathToFields[path_?EdgeListQ, edges_?QuiverEdgesQ] := 
  Module[{assoc},
    assoc = Association[edges];
    path // ReplaceAll[edges] // Outer[CenterDot, Sequence@@#1] & // Flatten
  ];


SyntaxInformation[GaugeInvariantMesons] = {"ArgumentsPattern" -> {_, _}};
GaugeInvariantMesons[edges: (_?QuiverEdgesQ | _?EdgeListQ), 
  degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] := 
    Flatten@QuiverPathToFields[QuiverCycles[edges, degspec], edges];
GaugeInvariantMesons[ edges: (_?QuiverEdgesQ | _?EdgeListQ), deg_] := 
  Flatten@QuiverPathToFields[QuiverCycles[edges, deg], edges];


SyntaxInformation[QuiverIncidenceMatrix] = {"ArgumentsPattern" -> {_}};
QuiverIncidenceMatrix[W_?PotentialQ] := 
  QuiverIncidenceMatrix[QuiverFromFields@W];
QuiverIncidenceMatrix[edges_?QuiverEdgesQ] := 
  QuiverIncidenceMatrix[KeysByValueLength@edges];
QuiverIncidenceMatrix[edges_?EdgeListQ] := 
  Module[{},
    IncidenceMatrix@Graph[
      Sort@VertexList@edges, 
      edges
    ] // Normal[-#] & 
  ];


SyntaxInformation[MesonQ] = {"ArgumentsPattern" -> {_}};
MesonQ[t : (_Times|_CenterDot)?FieldProductQ] :=
  MesonQ@FieldsToTaggedEdges[
    (List @@ t) /. {Power -> Splice@*ConstantArray}
  ];
MesonQ[e_?EdgeListQ] := AllTrue[
    QuiverIncidenceMatrix[e],
    (Count[#, 1] == Count[#, -1]) && (Count[#, 1] > 0) &
  ];
MesonQ[_] := False;


SyntaxInformation[MesonQ] = {"ArgumentsPattern" -> {_}};
OrderedMesonQ[c_CenterDot?FieldProductQ] :=
  OrderedMesonQ@FieldsToTaggedEdges[
    (List @@ c) /. {Power -> Splice@*ConstantArray}
  ];
OrderedMesonQ[e_?EdgeListQ] := 
  (SameQ[#1, RotateRight@#2] &) @@ 
    Transpose@Map[Take[List @@ #, 2] &, e];
OrderedMesonQ[_] := False;


SyntaxInformation[GaugeInvariantQ] = {"ArgumentsPattern" -> {_}};
GaugeInvariantQ[expr_] := 
  AllTrue[FieldProducts@expr, OrderedMesonQ];


SyntaxInformation[ReorderLoopEdges] = {"ArgumentsPattern" -> {_}};
ReorderLoopEdges::noloop = "List of edges does not correspond to a cycle \
of a composition of cycles.";
ReorderLoopEdges::arg = "Argument does not correspond to a list of edges.";
ReorderLoopEdges[e_List?MesonQ] :=
  Module[{incM, eeM, n, tree},
    n = Length[e];
    incM = Transpose@QuiverIncidenceMatrix[e];
    eeM = AssociationThread[
      Range[n],
      (Join @@ KeySelect[
        PositionIndex@incM,
        EqualTo[ FirstPosition[#,-1|2] ]@*FirstPosition[1|2]
      ] &) /@ incM];
    tree = Nest[
      Map[Splice@Thread@Join[#, {eeM[Last@#]}] &], 
      List /@ Range[n], 
      n-1];
    DeleteDuplicates[
      (e[[#]] &) /@ Select[tree, EqualTo[Range@n]@*Sort ],
      AnyTrue[ NestList[RotateLeft, #1, Length@#1], EqualTo@#2 ] &
    ]
  ];
ReorderLoopEdges[e_List?EdgeListQ] := Message[ReorderLoopEdges::noloop];
ReorderLoopEdges[_] := Message[ReorderLoopEdges::arg];


SyntaxInformation[Mesons] = {"ArgumentsPattern" -> {_}};
Mesons::fperr = "Field product `1` is not a meson.";
Mesons::meserr = "Meson `1` cannot be written \
as a unique single trace operator.";
Mesons[expr_?(Not@*FreeQ[_?FieldQ])] :=
  Module[{mesonfp, edgeL},
    mesonfp = Select[MesonQ]@FieldProducts[expr];
    edgeL = FieldsToTaggedEdges[
      (List @@@ mesonfp) /. {Power -> Splice@*ConstantArray}
    ];
    AssociationThread[
      mesonfp,
      Map[CenterDot @@ X @@@ # &, 
        ReorderLoopEdges /@ edgeL, 
      {2}]
    ]
  ];


SyntaxInformation[NonAbelianizeMesons] = {"ArgumentsPattern" -> {_}};
NonAbelianizeMesons::argfree = "Expression does not contain any fields.";
NonAbelianizeMesons[expr_?(Not@*FreeQ[_?FieldQ])] :=
  Module[{fp, mes, newExpr},
    fp = FieldProducts[expr];
    If[ AnyTrue[fp, Not@*MesonQ],
      Message[Mesons::fperr, SelectFirst[Not@*MesonQ]@fp];
      Return[expr]
    ];
    newExpr = expr /. {Times -> CenterDot};
    mes = Mesons[newExpr];
    If[ AnyTrue[mes, Length[#] > 1 &],
      Message[Mesons::meserr, First@SelectFirst[Length[#]>1&]@mes];
      Return[expr]
    ];
    newExpr /. Map[First, mes]
  ];
NonAbelianizeMesons[expr_] := expr /; Message[NonAbelianizeMesons::argfree];


SyntaxInformation[FindQuiverPaths] = {"ArgumentsPattern" -> {_, _, _, _}};
FindQuiverPaths[e_?QuiverEdgesQ, i_, j_, deg_] :=
  FindQuiverPaths[KeysByValueLength@e, i, j, deg];
FindQuiverPaths[e_?EdgeListQ, i_, j_, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] :=
  Switch[e,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, Join @@ (FindQuiverPaths[e, i, j, #, All] & /@ SortBy[First]@degspec);
  ]
FindQuiverPaths[e_?EdgeListQ, i_, j_, deg_] :=
  Switch[e,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, FindPath[e, i, j, deg, All] // 
      Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &]
  ]


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
SyntaxInformation[QuiverGraph] = {
  "ArgumentsPattern" -> {_, ___},
  "OptionsName" -> {
    "MultiplicityAsEdges", 
    "ArrowsPosition",
    "ArrowSize"}
};
QuiverGraph[W_?PotentialQ, opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[Automatic, QuiverFromFields@W, opts];
QuiverGraph[e : (_?EdgeListQ | _?QuiverEdgesQ), opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[Automatic, e, opts];
QuiverGraph[Automatic, e_?QuiverEdgesQ, opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[Automatic, KeysByValueLength@e, opts];
QuiverGraph[Automatic, e_?EdgeListQ, opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  QuiverGraph[ parseVertexGrouping[e], e, opts];
QuiverGraph[v: {(_Integer|{__Integer})..}, W_?PotentialQ, 
    opts: OptionsPattern[{QuiverGraph, Graph}] ] :=
  QuiverGraph[v, QuiverFromFields@W, opts];
QuiverGraph[v: {(_Integer | {__Integer}) ..}, e_?QuiverEdgesQ, 
    opts: OptionsPattern[{QuiverGraph, Graph}] ] :=
  QuiverGraph[v, KeysByValueLength@e, opts]
QuiverGraph[v: {(_Integer | {__Integer}) ..}, e_?EdgeListQ, 
    opts: OptionsPattern[{QuiverGraph, Graph}] ] := 
  Graph[
    Flatten@v,
    If[OptionValue["MultiplicityAsEdges"],
      Identity, Map[First]@*parseArrowheads]@e,
    Sequence @@ FilterRules[{opts}, Except[
      Union[Options@QuiverGraph, {EdgeShapeFunction}], 
      Options@Graph]
    ],
    VertexSize -> OptionValue["VertexSize"],
    VertexStyle -> OptionValue["VertexStyle"],
    VertexLabels -> OptionValue["VertexLabels"],
    VertexLabelStyle -> OptionValue["VertexLabelStyle"],
    VertexCoordinates -> parseVertexPositioning[v],
    EdgeStyle -> OptionValue["EdgeStyle"],
    EdgeShapeFunction -> If[
      OptionValue["MultiplicityAsEdges"],
      GraphElementData[{"FilledArrow", "ArrowSize" -> OptionValue["ArrowSize"]}],
      parseArrowheads[e, OptionValue["ArrowSize"], OptionValue["ArrowsPosition"] ]
    ]
  ];

parseVertexGrouping[e_?EdgeListQ] :=
  Module[{adj, gr, v},
    v = VertexList@e;
    adj = Normal@AdjacencyMatrix@e;
    gr = Values@PositionIndex@AssociationThread[v, adj];
    If[MatchQ[{{(Alternatives@@v)..}}]@gr, First@gr, gr]
  ];

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
      Map[{Count[-1]@#, Count[+1]@#, Count[0]@#} &] //
      ApplyAt[Arrowheads[Join @@ parsePos /@ {
        Table[{-s,b+(2*k-#1+1)*2*s/3}, {k,0,#1-1}],
        Table[{+s,f+(2*k-#2+1)*2*s/3}, {k,0,#2-1}],
        Table[{+s,f+(2*k-#3+1)*2*s/3}, {k,0,#3-1}]
      }] &, {1}] //
    KeyValueMap[shapeF]
  ];


End[]


EndPackage[]
