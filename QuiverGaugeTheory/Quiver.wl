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
PossibleMesonQ::usage = "";
MesonQ::usage = "";
GaugeInvariantQ::usage = "";
Mesons::usage = "";
ReorderLoopEdges::usage = "";
NonAbelianizeMesons::usage = "";
ZigZagPathQ::usage = "";
ZigZagPaths::usage = "";
ZigZagOrderings::usage = "";
ZigZagOperator::usage = "";
SpecularDual::usage = "";
FindQuiverPaths::usage = "";
QuiverGraph::usage = "";
MutateQuiver::usage = "";
ToricFaceInvolution::usage = "";
SeibergDual::usage = "";
ToricSeibergDualsGraph::usage = ""; 
IsomorphicModelQ::usage = "";
IsomorphicQuiverQ::usage = "";
FindModelIsomorphism::usage = "";


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
RelabelFieldMultiplicity[w_?PotentialQ] :=
  Module[{relabelR},
    relabelR = Join @@ KeyValueMap[
      {k, v} |-> MapIndexed[#1 -> X[First@k, Last@k, First@#2] &, Sort@v],
      GroupBy[Normal@QuiverFromFields[w], Last -> First]
    ];
    Simplify[w /. relabelR]
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
GaugeInvariantMesons[pot_?PotentialQ, deg_] := 
    GaugeInvariantMesons[QuiverFromFields@pot, deg];
GaugeInvariantMesons[edges: (_?QuiverEdgesQ | _?EdgeListQ), 
  degspec:{ ({_Integer, _Integer}|{_Integer}) .. }] := 
    Flatten@QuiverPathToFields[QuiverCycles[edges, degspec], edges];
GaugeInvariantMesons[ edges: (_?QuiverEdgesQ | _?EdgeListQ), deg_] := 
  Flatten@QuiverPathToFields[QuiverCycles[edges, deg], edges];
SetAttributes[GaugeInvariantMesons, {Protected, ReadProtected}];


SyntaxInformation[QuiverIncidenceMatrix] = {"ArgumentsPattern" -> {_}};
QuiverIncidenceMatrix[w_?PotentialQ] := 
  QuiverIncidenceMatrix[QuiverFromFields@w];
QuiverIncidenceMatrix[edges_?QuiverEdgesQ] := 
  QuiverIncidenceMatrix[Values@edges];
QuiverIncidenceMatrix[edges_?EdgeListQ] := 
  Normal[ -IncidenceMatrix@Graph[Sort@VertexList@edges, edges] ];
SetAttributes[QuiverIncidenceMatrix, {Protected, ReadProtected}];


SyntaxInformation[PossibleMesonQ] = {"ArgumentsPattern" -> {_}};
PossibleMesonQ[t : (_Times|_CenterDot)?FieldProductQ] :=
  PossibleMesonQ@FieldsToTaggedEdges[
    (List @@ t) /. {Power -> Splice@*ConstantArray}
  ];
PossibleMesonQ[e_?EdgeListQ] := AllTrue[
    QuiverIncidenceMatrix[e],
    (Count[#, 1] == Count[#, -1]) && (Count[#, 1] > 0) &
  ];
PossibleMesonQ[_] := False;
SetAttributes[PossibleMesonQ, {Protected, ReadProtected}];


SyntaxInformation[MesonQ] = {"ArgumentsPattern" -> {_}};
MesonQ[c_CenterDot?FieldProductQ] :=
  MesonQ@FieldsToTaggedEdges[
    (List @@ c) /. {Power -> Splice@*ConstantArray}
  ];
MesonQ[e_?EdgeListQ] := 
  (SameQ[#1, RotateRight@#2] &) @@ 
    Transpose@Map[Take[List @@ #, 2] &, e];
MesonQ[_] := False;
SetAttributes[MesonQ, {Protected, ReadProtected}];


SyntaxInformation[GaugeInvariantQ] = {"ArgumentsPattern" -> {_}};
GaugeInvariantQ[expr_] := AllTrue[FieldProducts@expr, MesonQ];
SetAttributes[GaugeInvariantQ, {Protected, ReadProtected}];


SyntaxInformation[ReorderLoopEdges] = {"ArgumentsPattern" -> {_}};
ReorderLoopEdges[e_List?PossibleMesonQ] :=
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
    mesonfp = Select[PossibleMesonQ]@FieldProducts[expr];
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
    If[ AnyTrue[fp, Not@*PossibleMesonQ],
      Message[Mesons::fperr, SelectFirst[Not@*PossibleMesonQ]@fp];
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
NonAbelianizeMesons[expr_?(FreeQ[_?FieldQ])] := expr;
NonAbelianizeMesons::argfree = "Expression does not contain any fields.";
SetAttributes[NonAbelianizeMesons, {Protected, ReadProtected}];


ZigZagPathQ[w_?ToricPotentialQ][zz_] :=
  ZigZagPathQ[zz, w];
ZigZagPathQ[zz_?MesonQ, w_?ToricPotentialQ] :=
  Module[{ord},
    ord = Map[
      Apply[Coefficient[DG[w, #1], 
        SelectFirst[FieldProducts@DG[w, #1], 
          MatchQ[HoldPattern[CenterDot][#2, ___] | #2] 
        ]
      ]& ],
      Partition[Apply[List, zz], 2, 1, {1, 1}]
    ];
    MatchQ[ord, {PatternSequence[1, -1] ..} | {PatternSequence[-1, 1] ..}]
  ];
ZigZagPathQ[_, w_?ToricPotentialQ] := False;
ZigZagPathQ[_, _] := False;
SetAttributes[ZigZagPathQ, {Protected, ReadProtected}];


ZigZagPaths[w_?ToricPotentialQ, f_, sgn_] :=
  Message[ZigZagPath::fargerr, f];
ZigZagPaths[w_?ToricPotentialQ, f_?FieldQ, sgn_] :=
  Message[ZigZagPath::oargerr, sgn];
ZigZagPaths[w_?ToricPotentialQ, f_?FieldQ, sgn : (1 | -1)] :=
  Message[ZigZagPath::farginv, f] /; FreeQ[w, f];
ZigZagPaths[w_?ToricPotentialQ, f_?FieldQ, sgn : (1 | -1)] :=
  Module[{whileF, zz, ord},
    whileF = Not@Or[
      Length[#] > 1 && SameQ[First@#, Last@#],
      MatchQ[Last@#, {_, 0}]
    ] &;
    {zz, ord} = Transpose@Most@NestWhileList[
      FirstCase[
        List @@ DG[w, First@#],
        Times[Last@#, HoldPattern[CenterDot][t_, ___]] :> {t, -Last@#},
        {First@#, 0}
      ] &,
      {f, sgn}, 
      whileF@*List, All
    ];
    If[Not@And[
        PossibleMesonQ[CenterDot @@ zz],
        AllTrue[Total /@ Partition[ord, 2, 1, {1, 1}], PossibleZeroQ]
      ],
      Return[$Failed],
      Return[CenterDot @@ zz]
    ]
  ];
ZigZagPaths[w_?ToricPotentialQ] :=
  Module[{fp},
    fp = FieldCases[w];
    Union@Flatten@Simplify@Outer[
      ZigZagPaths[w, #1, #2] &, fp, {1, -1}, 1]
  ];
ZigZagPath::fargerr = "Field `1` is not a valid chiral.";
ZigZagPath::farginv = "`1` is not present the provided potential.";
ZigZagPath::oargerr = "Sign argument `1` must be either +1 or -1.";
SetAttributes[ZigZagPath, {Protected, ReadProtected}];


ZigZagOrderings[w_?ToricPotentialQ, zz_?MesonQ] :=
  Module[{f1, f2, fterm1, sgn},
    {f1, f2} = Take[List @@ zz, 2];
    fterm1 = List @@ Expand@DG[w, f1];
    sgn = Coefficient[Total@fterm1,
      SelectFirst[FieldProducts@fterm1, 
        MatchQ[HoldPattern[CenterDot][f2, __]]
      ]
    ];
    sgn*Power[-1, 1 + Range@Length@zz]
  ] /; ZigZagPathQ[zz, w];
ZigZagOrderings[w_?ToricPotentialQ] :=
  AssociationMap[
    ZigZagOrderings[w, #] &,
    ZigZagPaths@w
  ];
SetAttributes[ZigZagOrderings, {Protected, ReadProtected}];


ZigZagOperator[w_?ToricPotentialQ, zz_?MesonQ, r : _Integer : 1] := 
  Module[{rmsgn},
    rmsgn = First@*Simplify@*Abs;
    KeyValueMap[Times]@GroupBy[
      DG[w, ##] & @@@ Partition[List @@ zz, 2, 1, {1, 1}],
      (2 Boole[#] - 1 &)@*MatchQ[HoldPattern[Times][-1, __]],
      (CenterDot@@Table[#, r] &)@*rmsgn@*Apply[CenterDot]@*Reverse
    ]
  ] /; ZigZagPathQ[zz, w];
ZigZagOperator[w_?ToricPotentialQ] := 
  AssociationMap[
    ZigZagOperator[w, #] &,
    ZigZagPaths@w
  ];
SetAttributes[ZigZagOperator, {Protected, ReadProtected}];


SpecularDual[w_?ToricPotentialQ] :=
  Module[{zzs, intersect, ord, ordered, rp},
    zzs = ZigZagPaths[w];
    intersect = AssociationThread[
      Subsets[Range@Length@zzs, {2}],
      Intersection @@@ Subsets[List @@@ zzs, {2}]
    ];
    selfIntersect = Association@MapIndexed[
      Join[#2, #2] -> #1[[
          First /@ Position[Boole@UpperTriangularize[Outer[SameQ, #1, #1], 1], 1]
        ]] &,
      List @@@ zzs
    ];
    ord = ZigZagOrderings[w, #] & /@ zzs;
    ordered = Association@KeyValueMap[
      {k, v} |-> KeyValueMap[
        If[#1 == {1, -1}, k, Reverse@k] -> v[[#2]] &,
        PositionIndex[Extract[ord[[k]], Position[zzs[[k]], #]] & /@ v]
      ],
      Join[intersect, selfIntersect]
    ];
    rp = KeyValueMap[
      {k, v} |-> Splice@MapIndexed[#1 -> (Subscript[X, First@#2] @@ k) &, v],
      ordered
    ];
    NonAbelianizeMesons[w /. rp]
  ];
SetAttributes[SpecularDual, {Protected, ReadProtected}];


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
QuiverGraph[w_?PotentialQ, opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[Automatic, QuiverFromFields@w, opts];
QuiverGraph[e : (_?EdgeListQ | _?QuiverEdgesQ), opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[Automatic, e, opts];
QuiverGraph[Automatic, e_?QuiverEdgesQ, opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[Automatic, Values@e, opts];
QuiverGraph[Automatic, e_?EdgeListQ, opts: OptionsPattern[QuiverGraph] ] := 
  QuiverGraph[ parseVertexGrouping[e], e, opts];
QuiverGraph[v: {(_Integer|{__Integer})..}, w_?PotentialQ, opts: OptionsPattern[QuiverGraph] ] :=
  QuiverGraph[v, QuiverFromFields@w, opts];
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
      Map[{Count[-1]@#, Count[1]@#, Count[0]@#} &] //
      ApplyAt[Arrowheads[Join @@ parsePos /@ {
        Table[{-s,b+(2*k-#1+1)*2*s/3}, {k,0,#1-1}],
        Table[{ s,f+(2*k-#2+1)*2*s/3}, {k,0,#2-1}],
        Table[{ s,f+(2*k-#3+1)*2*s/3}, {k,0,#3-1}]
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
  Fold[MutateQuiver, {q, ranks}, ks];
MutateQuiver[{q : (_?GraphQ | _?EdgeListQ), ranks : KeyValuePattern[_ -> _Integer]}, k_] :=
  Module[{a, v, i, n0, col, row, rk},
    v = VertexList[q];
    a = Normal@AdjacencyMatrix[q];
    i = VertexIndex[q, k];
    n0 = ranks[k];
    rk = Append[ranks, k -> 0];
    {col, row} = {a[[All, i]], a[[i, All]]};
    a[[All, i]] = row;
    a[[i, All]] = col;
    AppendTo[rk, k -> (Total[Map[rk, v]*row] - n0)];
    a = a + Outer[Times, col, row];
    a = Map[Max[0, #] &, a - Transpose[a], {2}];
    Return[{EdgeList@AdjacencyGraph[v, a], AssociationMap[rk, Keys@ranks]}];
  ];
MutateQuiver::rkerr = "The rank vector `1` does not have size `2`.";
MutateQuiver::verterr = "The `3` `2` does not appear in the graph `1`.";
SetAttributes[MutateQuiver, {Protected, ReadProtected}];


Options[SeibergDual] = {"Resolve" -> Automatic, "IntegrateMassive" -> True, "Relabel" -> True};
SeibergDual[v_, opts : OptionsPattern[SeibergDual]][w_?PotentialQ] :=
  SeibergDual[w, v, opts];
SeibergDual[v_, opts : OptionsPattern[SeibergDual]][{w_?PotentialQ, ranks: KeyValuePattern[_ -> _Integer]}] :=
  SeibergDual[{w, ranks}, v, opts];
SeibergDual[w_?PotentialQ, v_, opts : OptionsPattern[SeibergDual]] :=
  SeibergDual[{w, AssociationThread[VertexList@Values@QuiverFromFields@w, 1]}, v, opts];
SeibergDual[{w_?PotentialQ, ranks : KeyValuePattern[_ -> _Integer]}, v_, OptionsPattern[SeibergDual]] :=
  Module[{m, q, qc, quiv, toricSiebergQ, in, out, nc, nf, ij0, z0, comp, rp, newM, newW, resolveF, relabelF, z},
    {m, q, qc, z} = {\[FormalCapitalM], \[FormalCapitalQ], \[FormalCapitalC], \[FormalZeta]};
    quiv = QuiverFromFields@w;
    toricSiebergQ = MemberQ[v]@Extract[VertexList@Values@quiv,
      Position[Normal@IncidenceMatrix@Values@quiv, 
        l_List /; (Count[l, 1] == Count[l, -1] == 2), {1}]
    ];
    {in, out} = {
      Cases[Keys@quiv, Subscript[X, _][_, v]], 
      Cases[Keys@quiv, Subscript[X, _][v, _]]
    };
    nc = Lookup[Association@ranks, v, 1];
    nf = Total@Lookup[ranks, Last /@ out];
    ij0 = Map[Max]@Transpose@Join[
      Cases[w, m[i_, j_] :> {i, j}, Infinity], {0, 0}];
    z0 = Max@Join[Cases[w, z[i_] :> i, Infinity], {0}];
    comp = Association@Flatten@MapIndexed[
      #1 -> Subscript[X, m@@(ij0 + #2)][First@First@#1, Last@Last@#1] &,
      Outer[List, in, out, 1], {2}
    ];
    rp = KeyValueMap[
      ToCyclicPattern@HoldPattern[CenterDot][l___, First@#1, Last@#1, r___] :> CenterDot[l, #2, r] &, 
      comp
    ];
    newM = Flatten@MapIndexed[
      CenterDot[
        Subscript[X, q@First[ij0 + #2]] @@ Reverse[First@#1],
        Lookup[comp, Key@#1],
        Subscript[X, qc@Last[ij0 + #2]] @@ Reverse[Last@#1]
      ] &,
      Outer[List, in, out, 1], {2}
    ];
    resolveF = Switch[{OptionValue["Resolve"], toricSiebergQ},
      {Automatic | True, True} | {True, False},
      (# /. Last[Solve[0 == FTermsConstraint[#], Integers] /. C[_] -> 1, {}] &),
      _, Identity
    ];
    relabelF = If[OptionValue["Relabel"], 
      RelabelFieldMultiplicity, Identity];
    newW = resolveF[ReplaceAll[rp]@w + Array[z, Length@newM, z0 + 1].newM];
    newW = relabelF@If[OptionValue["IntegrateMassive"],
      IntegrateOutMassTerms@newW, relabelF@newW
    ];
    {newW, KeySort@Append[Association@ranks, v -> nf - nc]}
  ];
SeibergDual[{w : Except[_?PotentialQ], _}, _, OptionsPattern[SeibergDual]] :=
  Null /; Message[SeibergDual::warg, w];
SeibergDual[{_, ranks : Except@KeyValuePattern[_ -> _Integer]}, _, OptionsPattern[SeibergDual] ] :=
  Null /; Message[SeibergDual::rkarg, ranks];
SeibergDual[{w_?PotentialQ, ranks : KeyValuePattern[_ -> _Integer]}, _, 
    OptionsPattern[SeibergDual] ] /; !ContainsAll[Keys@ranks, VertexList@Values@QuiverFromFields@w] :=
  Null /; Message[SeibergDual::rkarg, ranks];
SeibergDual[{w_?PotentialQ, KeyValuePattern[_ -> _Integer]}, v_, OptionsPattern[SeibergDual] ] /; !PotentialMemberQ[w, v, 2] :=
  Null /; Message[SeibergDual::varg, v, w];
SeibergDual[{w_?PotentialQ, ranks : KeyValuePattern[_ -> _Integer]}, v_, OptionsPattern[SeibergDual] ] :=
  $Failed /; !And[ PotentialMemberQ[w, v, 2], 
    ContainsAll[Keys@ranks, VertexList@Values@QuiverFromFields@w] ];
SeibergDual::warg = "Argument `1` is not a valid potential.";
SeibergDual::rkarg = "Argument `1` is not a valid rank-integer association map.";
SeibergDual::varg = "Argument `1` is not a valid vertex in the potential `2`.";
SetAttributes[SeibergDual, {Protected, ReadProtected}];


Options[ToricFaceInvolution] := {"IntegrateMassive" -> True, "Relabel" -> True};
ToricFaceInvolution[v_, opts: OptionsPattern[ToricFaceInvolution] ][w_?ToricPotentialQ] :=
  ToricFaceInvolution[w, v, opts];
ToricFaceInvolution[w_?ToricPotentialQ, v_, OptionsPattern[ToricFaceInvolution] ] :=
  Module[{fp, w0, wf, relabelF, z},
    z = \[FormalCapitalZ];
    w0 = Select[Expand@w, FreeQ[ Subscript[X, _][_, v] | Subscript[X, _][v, _] ] ];
    fp = AssociationMap[
      ReplaceAll[{
        HoldPattern[CenterDot][l___, Subscript[X, i_][a_, v], Subscript[X, j_][v, b_], r___] :>
          {CenterDot[l, X[a, b, z[i, j]], r], -CenterDot[X[b, v, z[j]], X[v, a, z[i]], X[a, b, z[i, j]]]},
        HoldPattern[CenterDot][Subscript[X, j_][v, b_], c___, Subscript[X, i_][a_, v]] :>
          {CenterDot[X[a, b, z[i, j]], c], -CenterDot[X[b, v, z[j]], X[v, a, z[i]], X[a, b, z[i, j]]]}
      }],
      Select[
        FieldProducts@Expand@w, 
        Not@*FreeQ[Subscript[X, _][_, v] | Subscript[X, _][v, _]]
      ]
    ];
    relabelF = If[OptionValue["Relabel"], RelabelFieldMultiplicity, Identity];
    wf = relabelF[
      w0 + Total@KeyValueMap[Coefficient[w, #1] Total[#2] &, fp]
    ];
    If[OptionValue["IntegrateMassive"],
      relabelF@IntegrateOutMassTerms@wf, wf
    ]
  ];
ToricFaceInvolution[w : Except[_?ToricPotentialQ], _, OptionsPattern[ToricFaceInvolution] ] :=
  Null /; Message[ToricFaceInvolution::warg, w];
ToricFaceInvolution[w_?ToricPotentialQ, v_, OptionsPattern[ToricFaceInvolution] ] /; ! PotentialMemberQ[w, v, 2] :=
  Null /; Message[ToricFaceInvolution::varg, v, w];
ToricFaceInvolution[w_?ToricPotentialQ, v_, OptionsPattern[ToricFaceInvolution]] :=
  $Failed /; ! PotentialMemberQ[w, v, 2];
ToricFaceInvolution::warg = "Argument `1` is not a valid potential.";
ToricFaceInvolution::varg = "Argument `1` is not a valid vertex in the potential `2`.";
SetAttributes[ToricFaceInvolution, {Protected, ReadProtected}];


IsomorphicQuiverQ[w2_?PotentialQ][w1_?PotentialQ] :=
  IsomorphicQuiverQ[w1, w2];
IsomorphicQuiverQ[w1_?PotentialQ, w2_?PotentialQ] :=
  Module[{iso, toG},
    toG = Values@*QuiverFromFields;
    iso[foo_] := Length@FindGraphIsomorphism[Graph@Map[foo]@toG@w1, Graph@toG@w2] > 0;
    Or[iso[Identity], iso[Reverse]]
  ];


IsomorphicModelQ[w2_?PotentialQ][w1_?PotentialQ] :=
  IsomorphicModelQ[w1, w2];
IsomorphicModelQ[w1_?PotentialQ, w2_?PotentialQ] :=
  Module[{toCycles, c1, c2, isoF, toG, iso},
    toCycles[w_] := KeyMap[CyclicSort]@GroupBy[
      FieldProducts@w, (Apply[DirectedEdge, #, {1}] &)@*Apply[List] -> (Coefficient[w, #] &)
    ];
    {c1, c2} = Map[toCycles, {w1, w2}];
    toG = Values@*QuiverFromFields;
    isoF = FindGraphIsomorphism[Graph@#1, Graph@#2, All] &;
    iso[foo_, sgn_] := Map[
      And @@ Values@Merge[
        {KeyMap[CyclicSort@*(Map[foo, #, {0, 1}] &)@*ReplaceAll[Normal@#], sgn*c1], c2},
        If[1 == Length@#, False, ContainsExactly @@ #] &
      ] &,
      isoF[Map[foo]@toG@w1, toG@w2]
    ];
    Or @@ Join[ iso[Identity, 1], iso[Identity, -1], iso[Reverse, 1], iso[Reverse, -1] ]
  ];
SetAttributes[IsomorphicModelQ, {Protected, ReadProtected}];


FindModelIsomorphism[w2_?PotentialQ][w1_?PotentialQ] :=
  FindModelIsomorphism[w1, w2];
FindModelIsomorphism[w1_?PotentialQ, w2_?PotentialQ, n : (_Integer?Positive | All) : All] :=
  Module[{findMulRp, f1, toG, iso},
    toG = Values@*QuiverFromFields;
    findMulRp = Function[ww,
      Select[
        Join @@@ Tuples@Values@Merge[
          GroupBy[QuiverFromFields@#, Identity, Keys] & /@ {ww, w2},
          Apply@Function[{ff, ff2}, Map[Thread[ff -> #] &, Permutations@ff2]]
        ],
        AnyTrue[{w2 - (ww /. #), w2 + (ww /. #)}, PossibleZeroQ@*Simplify] &
      ]
    ];
    f1 = FieldCases[w1];
    iso[foo_] := Composition[
      Map[ ReplaceAll[c_CenterDot :> foo@c]@*ReplaceAll[Thread[f1 -> #]] & ],
      KeyValueMap[Splice[#1 /. #2] &]@*DeleteCases[{}],
      AssociationMap[ findMulRp[w1 /. Thread[f1 -> #1] /. {c_CenterDot :> foo@c}] &],
      Map[(f1 /. {Subscript[X, k_][i_, j_] :> Subscript[X, k]@@foo[{i, j}]} /. ChangeGroupIndices[Values@KeySort@#]) &]
    ]@FindGraphIsomorphism[Graph@Map[foo]@toG@w1, Graph@toG@w2, n];
    Join @@ MapThread[Take, {
      {iso[Identity], iso[Reverse]},
      Switch[n, _Integer, UpTo /@ {Ceiling[n/2], Floor[n/2]}, _, {All, All}]
    }]
  ];
SetAttributes[FindModelIsomorphism, {Protected, ReadProtected}];


sameCycSizeQ[w1_?PotentialQ, w2_?PotentialQ] :=
 SameQ @@ Map[KeySort@GroupBy[FieldProducts@#, Length, Length] &, {w1, w2}]


Options[ToricSeibergDualsGraph] = {MaxIterations -> Automatic, SameTest -> Automatic};
ToricSeibergDualsGraph[w_?ToricPotentialQ, opts : OptionsPattern[ToricSeibergDualsGraph]] :=
  Module[{maxIter, toQuiver, squareFaces, sameF, sameModelQ, mutateFaces, whileF, res},
    toQuiver = Values@*QuiverFromFields;
    maxIter = Switch[OptionValue[MaxIterations],
      _Integer?Positive, OptionValue[MaxIterations],
      Automatic, 50, _, 50];
    sameF = Switch[OptionValue[SameTest],
      _Function, OptionValue[SameTest],
      _, Function[{x,y}, And[IsomorphicQuiverQ[x,y],
          SameQ@@Map[KeySort@GroupBy[FieldProducts@#, Length, Length] &, {x, y}]
      ] ]
    ];
    sameModelQ[w1_, w2_] := sameF[w1, w2];
    sameModelQ[w2_][w1_] := sameF[w1, w2];
    squareFaces = (Extract[ VertexList@#, 
      Position[Normal@IncidenceMatrix@#, l_List /; (Count[l, 1] == Count[l, -1] == 2), 
      {1}] ] &)@*toQuiver;
    mutateFaces[pot_] := Thread@DirectedEdge[pot,
      DeleteDuplicates[(First@SeibergDual[pot, #] &) /@ squareFaces[pot], sameModelQ]
    ];
    whileF = And[
      MemberQ[1]@Map[Length, ConnectedComponents@#2],
      UnsameQ[#1, #2]
    ] &;
    res = NestWhile[
      Function[g,
        Block[{wList, newE, newV, isomR},
          wList = Flatten@Select[ConnectedComponents@g, EqualTo[1]@*Length];
          newE = Union[EdgeList@g, Flatten[mutateFaces /@ wList]];
          newV = Union[VertexList@g, VertexList@newE];
          isomR = Flatten@MapIndexed[
            Thread[Select[Take[newV, UpTo @@ #2], sameModelQ@#1] -> #1] &, 
            Rest@newV];
          Graph[Union[newV //. isomR], DeleteDuplicates[newE //. isomR]]
        ]
      ],
      Graph[{Simplify@w}, {}],
      whileF, 2,
      maxIter
    ];
    Graph[VertexList@res,
      Union[Sort@*UndirectedEdge @@@ EdgeList@res]
    ]
  ];
SetAttributes[ToricSeibergDualsGraph, {Protected, ReadProtected}];


End[]


EndPackage[]
