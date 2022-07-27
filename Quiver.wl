(* ::Package:: *)

Unprotect["QuiverGaugeTheory`Quiver`*"];
ClearAll["QuiverGaugeTheory`Quiver`*"];


BeginPackage["QuiverGaugeTheory`Quiver`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`"
}]


QuiverEdgesQ::usage = "";
FieldsToEdges::usage = "";
FieldsToTaggedEdges::usage = "";
QuiverFromFields::usage = "";
RelabelFieldMultiplicity::usage = "";
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
MutateQuiver::usage = "";
MutatePotential::usage = "";
FindAllToricDuals::usage = ""; 


$QuiverRotationByDegree = {3 -> Pi/2, 4 -> Pi/4, 5 -> Pi/10, 7 -> 3 Pi/14};
$QuiverVertexGroupingSpread = Pi/20;


Begin["`Private`"]


SyntaxInformation[QuiverEdgesQ] = {"ArgumentsPattern" -> {_}};
QuiverEdgesQ[KeyValuePattern[(_?FieldQ) -> _DirectedEdge] ] := True;
QuiverEdgesQ[_] := False;
SetAttributes[QuiverEdgesQ, {Protected, ReadProtected}];


SyntaxInformation[FieldsToEdges] = {"ArgumentsPattern" -> {_}};
FieldsToEdges[expr_] :=
  ReplaceAll[{Subscript[X, _] -> DirectedEdge}]@expr;
SetAttributes[FieldsToEdges, {Protected, ReadProtected}];


SyntaxInformation[FieldsToTaggedEdges] = {"ArgumentsPattern" -> {_}};
FieldsToTaggedEdges[expr_] :=
  ReplaceAll[{Subscript[X, k_][i_,j_] :> DirectedEdge[i, j, k]}]@expr;
SetAttributes[FieldsToTaggedEdges, {Protected, ReadProtected}];


SyntaxInformation[QuiverFromFields] = {"ArgumentsPattern" -> {_}};
QuiverFromFields[expr_] := AssociationMap[FieldsToEdges, FieldCases@expr];
SetAttributes[QuiverFromFields, {Protected, ReadProtected}];


SyntaxInformation[RelabelFieldMultiplicity] = {"ArgumentsPattern" -> {_}};
RelabelFieldMultiplicity[W_?PotentialQ] :=
  Module[{relabelR},
    relabelR = Join @@ KeyValueMap[
      {k, v} |-> MapIndexed[#1 -> X[First@k, Last@k, First@#2] &, Sort@v],
      GroupBy[Normal@QuiverFromFields[W], Last -> First]
    ];
    Simplify[W /. relabelR]
  ];
SetAttributes[RelabelFieldMultiplicity, {Protected, ReadProtected}];


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
  QuiverCycles[Values@edges, {kmin, kmax}];
QuiverCycles[edges_?EdgeListQ, {kmin_Integer, kmax: _Integer|Infinity}] :=
  Module[{cyc2up, cyc1},
    cyc2up = FindCycle[edges, {kmin, kmax}, All];
    cyc1 = Cases[edges, (DirectedEdge | UndirectedEdge)[i_, i_, ___] ] //
      DeleteDuplicates // Map[List];
    If[kmin <= 1 <= kmax, Join[cyc1, cyc2up], cyc2up]
  ];
SetAttributes[QuiverCycles, {Protected, ReadProtected}];


SyntaxInformation[QuiverPathToFields] = {"ArgumentsPattern" -> {_, _.}};
QuiverPathToFields[edges: (_?QuiverEdgesQ | _?EdgeListQ)][paths: {__?EdgeListQ}|_?EdgeListQ] := 
  QuiverPathToFields[paths, edges];
QuiverPathToFields[paths: {__?EdgeListQ}, edges: (_?QuiverEdgesQ | _?EdgeListQ)] :=
  QuiverPathToFields[#, edges] & /@ paths;
QuiverPathToFields[path_?EdgeListQ, edges_?EdgeListQ] := 
  QuiverPathToFields[path, 
    KeyValueMap[Splice@Thread[Table[Subscript[X, i]@@#1, {i, #2}] -> #1] &, Counts@edges]
  ];
QuiverPathToFields[path_?EdgeListQ, edges_?QuiverEdgesQ] := 
  Module[{assoc},
    assoc = GroupBy[Normal@edges, Last -> First];
    path // ReplaceAll[assoc] // Outer[CenterDot, Sequence@@#1] & // Flatten
  ];
SetAttributes[QuiverPathToFields, {Protected, ReadProtected}];


SyntaxInformation[GaugeInvariantMesons] = {"ArgumentsPattern" -> {_, _}};
GaugeInvariantMesons[edges: (_?QuiverEdgesQ | _?EdgeListQ), 
  degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] := 
    Flatten@QuiverPathToFields[QuiverCycles[edges, degspec], edges];
GaugeInvariantMesons[ edges: (_?QuiverEdgesQ | _?EdgeListQ), deg_] := 
  Flatten@QuiverPathToFields[QuiverCycles[edges, deg], edges];
SetAttributes[GaugeInvariantMesons, {Protected, ReadProtected}];


SyntaxInformation[QuiverIncidenceMatrix] = {"ArgumentsPattern" -> {_}};
QuiverIncidenceMatrix[W_?PotentialQ] := 
  QuiverIncidenceMatrix[QuiverFromFields@W];
QuiverIncidenceMatrix[edges_?QuiverEdgesQ] := 
  QuiverIncidenceMatrix[Values@edges];
QuiverIncidenceMatrix[edges_?EdgeListQ] := 
  Normal[ -IncidenceMatrix@Graph[Sort@VertexList@edges, edges] ];
SetAttributes[QuiverIncidenceMatrix, {Protected, ReadProtected}];


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
SetAttributes[MesonQ, {Protected, ReadProtected}];


SyntaxInformation[OrderedMesonQ] = {"ArgumentsPattern" -> {_}};
OrderedMesonQ[c_CenterDot?FieldProductQ] :=
  OrderedMesonQ@FieldsToTaggedEdges[
    (List @@ c) /. {Power -> Splice@*ConstantArray}
  ];
OrderedMesonQ[e_?EdgeListQ] := 
  (SameQ[#1, RotateRight@#2] &) @@ 
    Transpose@Map[Take[List @@ #, 2] &, e];
OrderedMesonQ[_] := False;
SetAttributes[OrderedMesonQ, {Protected, ReadProtected}];


SyntaxInformation[GaugeInvariantQ] = {"ArgumentsPattern" -> {_}};
GaugeInvariantQ[expr_] := AllTrue[FieldProducts@expr, OrderedMesonQ];
SetAttributes[GaugeInvariantQ, {Protected, ReadProtected}];


SyntaxInformation[ReorderLoopEdges] = {"ArgumentsPattern" -> {_}};
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
ReorderLoopEdges[_List?EdgeListQ] := Null /; Message[ReorderLoopEdges::noloop];
ReorderLoopEdges[_] := Null /; Message[ReorderLoopEdges::arg];
ReorderLoopEdges::noloop = "List of edges does not correspond to a cycle of a composition of cycles.";
ReorderLoopEdges::arg = "Argument does not correspond to a list of edges.";
SetAttributes[ReorderLoopEdges, {Protected, ReadProtected}];


SyntaxInformation[Mesons] = {"ArgumentsPattern" -> {_}};
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
Mesons::fperr = "Field product `1` is not a meson.";
Mesons::meserr = "Meson `1` cannot be written as a unique single trace operator.";
SetAttributes[Mesons, {Protected, ReadProtected}];


SyntaxInformation[NonAbelianizeMesons] = {"ArgumentsPattern" -> {_}};
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
NonAbelianizeMesons::argfree = "Expression does not contain any fields.";
SetAttributes[NonAbelianizeMesons, {Protected, ReadProtected}];


SyntaxInformation[FindQuiverPaths] = {"ArgumentsPattern" -> {_, _, _, _}};
FindQuiverPaths[e_?QuiverEdgesQ, i_, j_, deg_] :=
  FindQuiverPaths[Values@e, i, j, deg];
FindQuiverPaths[e_?EdgeListQ, i_, j_, degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] :=
  Switch[e,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, Join @@ (FindQuiverPaths[e, i, j, #, All] & /@ SortBy[First]@degspec);
  ];
FindQuiverPaths[e_?EdgeListQ, i_, j_, deg_] :=
  Switch[e,
    _?(FreeQ[i]), Missing["QuiverVertexAbsent", i],
    _?(FreeQ[j]), Missing["QuiverVertexAbsent", j],
    _, FindPath[e, i, j, deg, All] // 
      Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &]
  ];
SetAttributes[FindQuiverPaths, {Protected, ReadProtected}];


Options[QuiverGraph] = Normal@Association@{
  Splice@Options[Graph],
  ImageSize -> 250,
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
  "ArgumentsPattern" -> {_, _., OptionsPattern[]}
};
QuiverGraph[W_?PotentialQ, opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[Automatic, QuiverFromFields@W, opts];
QuiverGraph[e : (_?EdgeListQ | _?QuiverEdgesQ), opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[Automatic, e, opts];
QuiverGraph[Automatic, e_?QuiverEdgesQ, opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[Automatic, Values@e, opts];
QuiverGraph[Automatic, e_?EdgeListQ, opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[ parseVertexGrouping[e], e, opts];
QuiverGraph[v: {(_Integer|{__Integer})..}, W_?PotentialQ, opts: OptionsPattern[QuiverGraph] ] :=
  QuiverGraph[v, QuiverFromFields@W, opts];
QuiverGraph[v: {(_Integer | {__Integer}) ..}, e_?QuiverEdgesQ, opts: OptionsPattern[QuiverGraph] ] :=
  QuiverGraph[v, Values@e, opts]
QuiverGraph[v: {(_Integer | {__Integer}) ..}, e_?EdgeListQ, opts: OptionsPattern[QuiverGraph] ] :=
  Module[{edges, edgeShapeF},
    edges = If[OptionValue["MultiplicityAsEdges"],
      e, Map[First]@parseArrowheads@e];
    edgeShapeF = If[OptionValue["MultiplicityAsEdges"],
      GraphElementData[{"FilledArrow", "ArrowSize" -> OptionValue["ArrowSize"]}],
      parseArrowheads[e, OptionValue["ArrowSize"], OptionValue["ArrowsPosition"] ]
    ];
    Graph[Flatten@v, edges,
      Sequence @@ FilterRules[FilterRules[{opts}, Options@QuiverGraph], 
        Except[{EdgeShapeFunction, "MultiplicityAsEdges", "ArrowSize", "ArrowsPosition"}]
      ],
      ImageSize -> OptionValue["ImageSize"],
      VertexSize -> OptionValue["VertexSize"],
      VertexStyle -> OptionValue["VertexStyle"],
      VertexLabels -> OptionValue["VertexLabels"],
      VertexLabelStyle -> OptionValue["VertexLabelStyle"],
      EdgeStyle -> OptionValue["EdgeStyle"],
      (*handling different layouts*)
      VertexCoordinates -> Switch[OptionValue["GraphLayout"],
        "CircularAdjacencyEmbedding" | Automatic,
        parseVertexPositioning[v],
        _, Automatic
      ],
      EdgeShapeFunction -> edgeShapeF
    ]
  ];
SetAttributes[QuiverGraph, {Protected, ReadProtected}];


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


MutateQuiver[k_][x: {(_?GraphQ | _?EdgeListQ), ({__Integer} | KeyValuePattern[_ -> _Integer])} | _?GraphQ | _?EdgeListQ] :=
  MutateQuiver[x, k];
MutateQuiver[{q: (_?GraphQ | _?EdgeListQ), ranks: ({__Integer} | KeyValuePattern[_ -> _Integer])}, ks_List] /; 
  (!SubsetQ[VertexList@q, ks]) := Null /; Message[MutateQuiver::verterr, EdgeList@q, ks, "vertices"];
MutateQuiver[{q: (_?GraphQ | _?EdgeListQ), ranks: ({__Integer} | KeyValuePattern[_ -> _Integer])}, k: Except[_List] ] /;
  (!MemberQ[VertexList@q, k]) := Null /; Message[MutateQuiver::verterr, EdgeList@q, k, "vertex"];
MutateQuiver[{q: (_?GraphQ | _?EdgeListQ), ranks: {__Integer}}, k_] /;
  UnsameQ[Length@ranks, Length@VertexList@q] := Null /; Message[MutateQuiver::rkerr, ranks, Length@VertexList@q];
MutateQuiver[q: (_?GraphQ | _?EdgeListQ), k_] :=
  MutateQuiver[{q, AssociationThread[VertexList@Graph@q, 1]}, k];
MutateQuiver[{q: (_?GraphQ | _?EdgeListQ), ranks: {__Integer}}, k_] :=
  MutateQuiver[{Graph@q, AssociationThread[VertexList@Graph@q, ranks]}, k];
MutateQuiver[{q: (_?GraphQ | _?EdgeListQ), ranks: ({__Integer} | KeyValuePattern[_ -> _Integer])}, ks_List] :=
  Fold[MutateQuiver, {Graph@q, ranks}, ks];
MutateQuiver[{q : (_?GraphQ | _?EdgeListQ), ranks : KeyValuePattern[_ -> _Integer]}, k_] :=
  Module[{a, V, i, n0, col, row, rk},
    V = VertexList[q];
    a = Normal@AdjacencyMatrix[q];
    i = VertexIndex[q, k];
    n0 = ranks[k];
    rk = Append[ranks, k -> 0];
    {col, row} = {a[[All, i]], a[[i, All]]};
    a[[All, i]] = row;
    a[[i, All]] = col;
    AppendTo[rk, k -> (Total[Map[rk, V]*row] - n0)];
    a = a + Outer[Times, col, row];
    a = Map[Max[0, #] &, a - Transpose[a], {2}];
    Return[{EdgeList@AdjacencyGraph[V, a], AssociationMap[rk, Keys@ranks]}];
  ];
MutateQuiver::rkerr = "The rank vector `1` does not have size `2`.";
MutateQuiver::verterr = "The `3` `2` does not appear in the graph `1`.";
SetAttributes[MutateQuiver, {Protected, ReadProtected}];


MutatePotential[k_][x: {_?PotentialQ, ({__Integer} | KeyValuePattern[_ -> _Integer])} | _?PotentialQ] :=
  MutatePotential[x, k];
MutatePotential[{W_?PotentialQ, ranks: ({__Integer} | KeyValuePattern[_ -> _Integer])}, ks_List] /; 
  (!SubsetQ[VertexList@Values@QuiverFromFields@W, ks]) := Null /; Message[MutatePotential::verterr, W, ks, "group labels"];
MutatePotential[{W_?PotentialQ, ranks: ({__Integer} | KeyValuePattern[_ -> _Integer])}, k: Except[_List] ] /; 
  (!MemberQ[VertexList@Values@QuiverFromFields@W, k]) := Null /; Message[MutatePotential::verterr, W, k, "group label"];
MutatePotential[{W_?PotentialQ, ranks: {__Integer}}, k_] /; UnsameQ[Length@ranks, Length@VertexList@Values@QuiverFromFields@W] :=
  Null /; Message[MutatePotential::rkerr, ranks, Length@VertexList@Values@QuiverFromFields@W];
MutatePotential[{W_?PotentialQ, ranks: ({__Integer} | KeyValuePattern[_ -> _Integer])}, ks_List] :=
  Fold[MutatePotential, {W, ranks}, ks];
MutatePotential[{W_?PotentialQ, ranks: {__Integer}}, k_] :=
  MutatePotential[{W, AssociationThread[VertexList@Values@QuiverFromFields@W, ranks]}, k];
MutatePotential[W_?PotentialQ, k_] :=
  MutatePotential[{W, KeySort@AssociationThread[VertexList@Values@QuiverFromFields@W, 1]}, k];
MutatePotential[{W_?PotentialQ, ranks: KeyValuePattern[_ -> _Integer]}, k_] :=
  Module[{f, in, out, comp0, comp, rep, revInOut, newMes, newW, zz, yy, startI},
    f = FieldCases@W;
    {in, out} = {Cases[f, Subscript[X, _][_, k] ], Cases[f, Subscript[X, _][k, _] ]};
    comp = Association@Flatten[ Thread /@ KeyValueMap[
      Table[(Subscript[X, zz@l] @@ #1), {l, Length@#2}] -> #2 &,
      GroupBy[Tuples[{in, out}], Replace[{Subscript[X, _][i_, _], Subscript[X, _][_, j_]} :> {i, j}] ] 
    ] ];
    rep = KeyValueMap[
      ToCyclicPattern@HoldPattern[CenterDot][l___, First@#2, Last@#2, r___] :> CenterDot[l, #1, r] &,
      comp
    ];
    revInOut = Flatten@Map[ KeyValueMap[
        Thread[#2 -> Table[Subscript[X, yy@l] @@ #1, {l, Length@#2}] ] &
      ]@*GroupBy[ Apply[Reverse@*List] ], 
      {out, in}
    ];
    newMes = KeyValueMap[
      Simplify[ CenterDot @@ Insert[#2, #1, 2] ] &, 
      ReplaceAll[revInOut] /@ comp
    ];
    startI = 1 + Max@Union[Cases[W, \[FormalZeta][i_] :> i, Infinity], {0}];
    newW = ReplaceAll[rep]@W + Array[\[FormalZeta], Length@newMes, startI].newMes // Expand;
    {
      RelabelFieldMultiplicity@IntegrateOutMassTerms[newW],
      KeySort@Last@MutateQuiver[{DirectedEdge @@@ f, ranks}, k]
    }
  ];
MutatePotential::rkerr = "The rank vector `1` does not have size `2`.";
MutatePotential::verterr = "The `3` `2` does not appear in the potential `1`.";
SetAttributes[MutateQuiver, {Protected, ReadProtected}];


FindAllToricDuals[W_?ToricPotentialQ, maxIter: _Integer?Positive : 15] :=
  Module[{toQuiver, squareFaces, resolveToric, mutateSquareFaces, sameModelQ, visited, isomR},
    toQuiver = Values@*QuiverFromFields;
    sameModelQ[w1_][w2_] := sameModelQ[w1, w2];
    sameModelQ[w1_, w2_] := Or[
      Length@FindGraphIsomorphism[Graph@toQuiver@w1, Graph@toQuiver@w2] > 0,
      Length@FindGraphIsomorphism[Graph@toQuiver@w1, Graph@Map[Reverse]@toQuiver@w2] > 0
    ];
    squareFaces = Extract[VertexList@#, Position[Normal@IncidenceMatrix@#,
       l_List /; (Count[l, 1] == Count[l, -1] == 2), {1}]
    ] &;
    resolveToric = (# /. Last[Solve[FTermsConstraint[#] == 0], {}] &);
    mutateSquareFaces[pot_] := Thread@UndirectedEdge[pot, DeleteDuplicates[
      (resolveToric@First@MutatePotential[pot, #] &) /@ squareFaces[toQuiver@pot],
      sameModelQ]
    ];
    visited = {};
    FixedPoint[
      Function[g, 
        Block[{wList, newE, newV},
          wList = DeleteCases[VertexList@g, Alternatives @@ visited];
          visited = Union[visited, wList];
          newE = Union[EdgeList@g, Flatten[mutateSquareFaces /@ wList] ];
          newV = Union[VertexList@g, VertexList@newE];
          isomR = Flatten@MapIndexed[
            Thread[Select[sameModelQ@#1]@Take[newV, UpTo@First@#2] -> #1] &,
            Rest@newV
          ];
          Graph[
            DeleteDuplicates[newV //. isomR],
            DeleteCases[DeleteDuplicates[Sort /@ (newE //. isomR)], 
              HoldPattern[UndirectedEdge][z_, z_] ] 
          ]
        ] 
      ],
      Graph[{Simplify@W}, {}],
      maxIter
    ]
  ];
SetAttributes[FindAllToricDuals, {Protected, ReadProtected}];


End[]


EndPackage[]
