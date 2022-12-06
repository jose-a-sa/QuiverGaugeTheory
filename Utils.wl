(* ::Package:: *)

Unprotect["QuiverGaugeTheory`Utils`*"];
ClearAll["QuiverGaugeTheory`Utils`*"];


BeginPackage["QuiverGaugeTheory`Utils`"]


ContainsQ::usage = "";
ApplyAt::usage = "";
FirstLast::usage = "";
SymmetricDifference::usage = "";
SelectDelete::usage = "";
EdgeListQ::usage = "";
AssociationDepth::usage = "";
AssociationFlatten::usage = "";
KeysByValueLength::usage = "";
KeyValueReverse::usage = "";
AssociationTableToPairs::usage = "";
MinMaxExponent::usage = "";
CyclicRange::usage = "";
CyclicSort::usage = "";
CyclicPatternSequence::usage = "";
ToCyclicPattern::usage = "";
ToSubtractList::usage = "";
NormalizeGCD::usage = "";
TransformedMesh::usage = "";
CollinearQ::usage = "";
StrictlyCollinearQ::usage = "";
CoplanarQ::usage = "";
StrictlyCoplanarQ::usage = "";
UniqueCases::usage = "";
IndexedList::usage = "";

GridRulesGraphics::usage = "";
ConicalSimplexHullRegion::usage = "";

AcuteCone::usage = "";
DualCone::usage = "";

FindNonSimplePaths::usage = "";
SolveMatrixLeft::usage = "";

UsageForm::usage = "";
ReapMessages::usage = "";
EchoUniqueMessages::usage = "";


Begin["`Private`"]


SyntaxInformation[ContainsQ] = {"ArgumentsPattern" -> {_, _., _.}};
ContainsQ[form_] := (Not@*FreeQ[form]);
ContainsQ[expr_, y__] := (Not@FreeQ[expr, y]);
SetAttributes[ContainsQ, {Protected, ReadProtected}];


SyntaxInformation[ApplyAt] = {"ArgumentsPattern" -> {_, _.}};
ApplyAt[f_, levelspec_ : {0}] := 
  Apply[f, #, levelspec] &;
SetAttributes[ApplyAt, {Protected, ReadProtected}];


SyntaxInformation[FirstLast] = {"ArgumentsPattern" -> {_}};
FirstLast[expr_] := {First@expr,Last@expr};
SetAttributes[FirstLast, {Protected, ReadProtected}];


If[Null === Definition[SymmetricDifference],
  SyntaxInformation[SymmetricDifference] = {"ArgumentsPattern" -> {__}};
  SymmetricDifference[r__] := Complement[ Union[r], Intersection[r] ];
  SetAttributes[SymmetricDifference, {Flat, Protected, ReadProtected}];
];


SyntaxInformation[SelectDelete] = {"ArgumentsPattern" -> {_,_.,_.}};
SelectDelete[crit_][list_] := SelectDelete[list, crit];
SelectDelete[list_, crit_, n_ : Infinity] :=
  {Select[list, crit, n], Select[list, Not@*crit, n]};
SetAttributes[SelectDelete, {Protected, ReadProtected}];


SyntaxInformation[EdgeListQ] = {"ArgumentsPattern" -> {_}};
EdgeListQ[expr_] := 
  MatchQ[expr, { (DirectedEdge[__]|UndirectedEdge[__]) .. }];
SetAttributes[EdgeListQ, {Protected, ReadProtected}];


SyntaxInformation[KeysByValueLength] = {"ArgumentsPattern" -> {_}};
KeysByValueLength[a : KeyValuePattern[{}] ] :=
  KeyValueMap[Splice@Table[#1, Length@#2] &, Association@a];
SetAttributes[KeysByValueLength, {Protected, ReadProtected}];


SyntaxInformation[KeyValueReverse] = {"ArgumentsPattern" -> {_}};
KeyValueReverse[a : KeyValuePattern[{}] ] :=
  Association@KeyValueMap[#2 -> #1 &, Association@a];
SetAttributes[KeyValueReverse, {Protected, ReadProtected}];


SyntaxInformation[AssociationDepth] = {"ArgumentsPattern" -> {_}};
AssociationDepth[a : KeyValuePattern[{}] ] :=
  Module[{},
    Length@Rest@NestWhileList[
      Map[Splice]@*Values, {Association@a},
      (AllTrue[#1, MatchQ[_Association] ] && MatchQ[#1, Except[{}] ] &)
    ]
  ];
SetAttributes[AssociationDepth, {Protected, ReadProtected}];


SyntaxInformation[AssociationFlatten] = {"ArgumentsPattern" -> {_,_.}};
AssociationFlatten[a : KeyValuePattern[{}] ] :=
  Module[{n, flatten2, res},
    n = AssociationDepth[a];
    flatten2 = Association@*KeyValueMap[
      {t, r} |-> KeyValueMap[Splice@Prepend[{#1}, t] -> #2 &, Association@r]
    ];
    res = Nest[flatten2, Association@a, n - 1];
    KeyMap[List, res]
  ];
AssociationFlatten[a : KeyValuePattern[{}], max_Integer?NonNegative] :=
  AssociationFlatten[a, {Select[Range[AssociationDepth@a], LessEqualThan[max+1] ]}];
AssociationFlatten[a : KeyValuePattern[{}], 0 | {}] := 
  Association[a];
AssociationFlatten[a : KeyValuePattern[{}], max_Integer] :=
  Null /; Message[AssociationFlatten::flev, max, 2, a];
AssociationFlatten[a : KeyValuePattern[{}], {i__Integer}] :=
  AssociationFlatten[a, {{i}}];
AssociationFlatten[a : KeyValuePattern[{}], lvlspec : Except[{{__Integer?Positive} ..}] ] := 
  Null /; Message[AssociationFlatten::flpi, lvlspec];
AssociationFlatten[a : KeyValuePattern[{}], lvlspec : {{__Integer?Positive} ..}] /; 
  MatchQ[lvlspec, Except[{{__Integer?(LessEqualThan[AssociationDepth@a])} ..}] ] :=
    Null /; Message[AssociationFlatten::fldep,
      First@Cases[lvlspec, _Integer?(GreaterThan[AssociationDepth@a]), Infinity],
      lvlspec, AssociationDepth@a, Association@a
    ];
AssociationFlatten[a : KeyValuePattern[{}], lvlspec : {{__Integer?Positive} ..}] /;
   AnyTrue[Counts@Flatten[lvlspec], GreaterThan[1] ] := 
      Null /; Message[AssociationFlatten::flrep, 
        First@Keys@Select[Counts@Flatten[lvlspec], GreaterThan[1] ], 
        lvlspec
      ];
AssociationFlatten[a : KeyValuePattern[{}], lvlspec : {{__Integer} ..}] :=
  Module[{n, lvls, groupF, reshapeF},
    n = AssociationDepth[a];
    lvls = Join[lvlspec, List /@ Complement[Range[n], Join @@ lvlspec] ];
    groupF[p_] := GroupBy[(#[[p /. {x_} :> x]] &)@*First];
    reshapeF = Fold[{f, p} |-> Composition[ Map[f], groupF[p] ], groupF[Last@lvls], Most@lvls];
    Map[Last@*Last, reshapeF@Normal@AssociationFlatten[a], {Length@lvls}]
  ];
AssociationFlatten::fldep = Flatten::fldep;
AssociationFlatten::flpi = Flatten::flpi;
AssociationFlatten::flrep = Flatten::flrep;
AssociationFlatten::flev = Flatten::flev;
SetAttributes[AssociationFlatten, {Protected, ReadProtected}];


SyntaxInformation[MinMaxExponent] = {"ArgumentsPattern" -> {_, _.}};
MinMaxExponent[patt_][expr_] :=
  MinMaxExponent[expr, patt];
MinMaxExponent[expr_, patt_] := 
  MinMax@Exponent[
    MonomialList@ExpandAll[expr /. {x: patt :> \[FormalLambda] x}], 
    \[FormalLambda]
  ];
SetAttributes[MinMaxExponent, {Protected, ReadProtected}];


SyntaxInformation[CyclicSort] = {"ArgumentsPattern" -> {_}};
CyclicSort[x_] := RotateLeft[x, First@Ordering[x] - 1];
SetAttributes[CyclicSort, {Protected, ReadProtected}];


SyntaxInformation[CyclicRange] = {"ArgumentsPattern" -> {_, _., _., _.}};
CyclicRange[m_?Positive][i_Integer, f_Integer, s : _Integer?Positive : 1] := 
  CyclicRange[i, f, s, m];
CyclicRange[f_Integer, m_?Positive] := 
  CyclicRange[1, f, 1, m];
CyclicRange[i_Integer, f_Integer, m_Integer?Positive] :=
  CyclicRange[i, f, 1, m];
CyclicRange[i_Integer, f_Integer, s_Integer?Positive, m_Integer?Positive] := 
  ReplaceAll[0 -> m]@Mod[Range[i, i + Mod[f - i, m], s], m];
SetAttributes[CyclicRange, {Protected, ReadProtected}];


SyntaxInformation[CyclicPatternSequence] = {"ArgumentsPattern" -> {___}};
CyclicPatternSequence[patt__] := Alternatives @@ NestList[
  RotateRight, PatternSequence[patt], Length[{patt}] - 1]
CyclicPatternSequence[] := PatternSequence[];
SetAttributes[CyclicPatternSequence, {Protected, ReadProtected}];


SyntaxInformation[ToCyclicPattern] = {"ArgumentsPattern" -> {_}};
ToCyclicPattern[ x_ ] := 
  Alternatives @@ NestList[RotateRight, x, Length@x -1];
SetAttributes[ToCyclicPattern, {Protected, ReadProtected}];


SyntaxInformation[ToSubtractList] = {"ArgumentsPattern" -> {_}};
ToSubtractList[ expr : _Equal ] := ToSubtractList[{expr}];
ToSubtractList[ expr : (List|And)[Except[_List]..] ] := 
  Map[ Through@*If[MatchQ[_Equal], Apply[Subtract], Identity],
    List @@ expr
  ];
SetAttributes[ToSubtractList, {Protected, ReadProtected}];


SyntaxInformation[NormalizeGCD] = {"ArgumentsPattern" -> {_}};
NormalizeGCD[p: {0 ..}] := p; 
NormalizeGCD[p: {__?ExactNumberQ}] := p / (GCD @@ p);
NormalizeGCD[p: {__}] := p;
SetAttributes[NormalizeGCD, {Protected, ReadProtected}];


TransformedMesh[t_][m_MeshRegion] := 
  TransformedMesh[m, t]
TransformedMesh[m_MeshRegion, t : {{__?NumericQ} ..}?MatrixQ] := 
  Message[TransformedMesh::dimerr] /; 
    Apply[Unequal, {Splice@Dimensions[t], Length@First@MeshCoordinates[m]}];
TransformedMesh[m_MeshRegion, t : {{__?NumericQ} ..}?SquareMatrixQ] :=
  MeshRegion[
    Map[x |-> t . x, Rationalize@MeshCoordinates@m],
    MeshCells@m,
    Sequence @@ Options[m]
  ];
TransformedMesh[m_MeshRegion, _] := Null /; Message[TransformedMesh::matarg]
TransformedMesh::dimerr = "Dimension of the mesh points and the transformation matrix do not match.";
TransformedMesh::matarg = "Argument provided is not a valid argument.";
SetAttributes[TransformedMesh, {Protected, ReadProtected}];


SyntaxInformation[CollinearQ] = {"ArgumentsPattern" -> {_}};
CollinearQ[{}] := Null /; ArgumentCountQ[CollinearQ, 0, 1, 1];
CollinearQ[{_}?MatrixQ] := True;
CollinearQ[{pts__}?MatrixQ] := 
  MatrixRank@Map[# - First[{pts}] &, Rest@{pts}] <= 1 /; (Length[{pts}] > 1);
CollinearQ[x : Except[_List] ] := Null /; Message[CollinearQ::pts, x];
CollinearQ[x_, y__] := Null /; ArgumentCountQ[CollinearQ, Length[{x, y}], 1, 1];
CollinearQ::pts = "`1` should be a non-empty list of points.";
SetAttributes[CollinearQ, {Protected, ReadProtected}];


SyntaxInformation[StrictlyCollinearQ] = {"ArgumentsPattern" -> {_}};
StrictlyCollinearQ[{}] := Null /; ArgumentCountQ[StrictlyCollinearQ, 0, 1, 1];
StrictlyCollinearQ[{_}?MatrixQ] := True;
StrictlyCollinearQ[{pts__}?MatrixQ] := 
  MatrixRank@Map[# - First[{pts}] &, Rest@{pts}] == 1 /; (Length[{pts}] > 1);
StrictlyCollinearQ[x : Except[_List] ] := Null /; Message[StrictlyCollinearQ::pts, x];
StrictlyCollinearQ[x_, y__] := Null /; ArgumentCountQ[StrictlyCollinearQ, Length[{x, y}], 1, 1];
StrictlyCollinearQ::pts = "`1` should be a non-empty list of points.";
SetAttributes[StrictlyCollinearQ, {Protected, ReadProtected}];


SyntaxInformation[CoplanarQ] = {"ArgumentsPattern" -> {_}};
CoplanarQ[{}] := Null /; ArgumentCountQ[CoplanarQ, 0, 1, 1];
CoplanarQ[{_}?MatrixQ] := True;
CoplanarQ[{pts__}?MatrixQ] := 
  MatrixRank@Map[# - First[{pts}] &, Rest@{pts}] <= 2 /; (Length[{pts}] > 1);
CoplanarQ[x : Except[_List] ] := Null /; Message[CoplanarQ::pts, x];
CoplanarQ[x_, y__] := Null /; ArgumentCountQ[CoplanarQ, Length[{x, y}], 1, 1];
CoplanarQ::pts = "`1` should be a non-empty list of points.";
SetAttributes[CoplanarQ, {Protected, ReadProtected}];


SyntaxInformation[StrictlyCoplanarQ] = {"ArgumentsPattern" -> {_}};
StrictlyCoplanarQ[{}] := Null /; ArgumentCountQ[StrictlyCoplanarQ, 0, 1, 1];
StrictlyCoplanarQ[{_}?MatrixQ] := True;
StrictlyCoplanarQ[{pts__}?MatrixQ] := 
  MatrixRank@Map[# - First[{pts}] &, Rest@{pts}] == 2 /; (Length[{pts}] > 1);
StrictlyCoplanarQ[x : Except[_List] ] := Null /; Message[StrictlyCoplanarQ::pts, x];
StrictlyCoplanarQ[x_, y__] := Null /; ArgumentCountQ[StrictlyCoplanarQ, Length[{x, y}], 1, 1];
StrictlyCoplanarQ::pts = "`1` should be a non-empty list of points.";
SetAttributes[StrictlyCoplanarQ, {Protected, ReadProtected}];


SyntaxInformation[UniqueCases] = SyntaxInformation[Cases];
Options[UniqueCases] = Options[Cases];
UniqueCases[pattern_, opts : OptionsPattern[Cases] ][expr_] :=
  UniqueCases[expr, pattern, opts];
UniqueCases[expr_, pattern_, opts : OptionsPattern[Cases] ] :=
  DeleteDuplicates@Cases[expr, pattern, Infinity, opts];
SetAttributes[UniqueCases, {Protected, ReadProtected}];


SyntaxInformation[IndexedList] = {"ArgumentsPattern" -> {_, _., _.}};
IndexedList[l_List] := Transpose[{Range@Length@l, l}];
IndexedList[l_List, n0_] := 
  Transpose[{Range[n0, Length[l] + (n0 - 1)], l}];
IndexedList[l_List, n0_, di_] := 
  Transpose[{Range[n0, n0 + di (Length[l] - 1), di], l}];
SetAttributes[IndexedList, {Protected, ReadProtected}];


SyntaxInformation[GridRulesGraphics] = {"ArgumentsPattern" -> {_,_.}};
GridRulesGraphics[
    {{bx_Integer, by_Integer}, {tx_Integer, ty_Integer}}, 
    color : (_?ColorQ) : GrayLevel[1/3, 1/3] ] :=
  Graphics[{color,
    Line /@ Join[
      Table[{{x, by}, {x, ty}}, {x, bx, tx, 1}],
      Table[{{bx, y}, {tx, y}}, {y, by, ty, 1}]
    ]}
  ] /; (tx > bx) && (ty > by)
SetAttributes[GridRulesGraphics, {Protected, ReadProtected}];


ConicalSimplexHullRegion[{} | {{}}, w_List?MatrixQ] :=
  ConicHullRegion[{ConstantArray[0, Last@Dimensions@w]}, w];
ConicalSimplexHullRegion[p_List?MatrixQ] :=
  Simplex[p];
ConicalSimplexHullRegion[p_List?MatrixQ, w_List?MatrixQ] :=
  ConicalSimplexHullRegion[Simplex[p], w];
ConicalSimplexHullRegion[reg_?RegionQ, {} | {{}}] :=
  reg;
ConicalSimplexHullRegion[reg_?RegionQ, w_List?MatrixQ] /; 
    (RegionEmbeddingDimension[reg] === Last[Dimensions@w, 0]) :=
  Module[{ts, us, t, u, restr, par, xs},
    us = Array[u, RegionEmbeddingDimension@reg];
    ts = Array[t, Length@w];
    restr = And @@ Join[Thread[ts >= 0], {Element[us, reg]}];
    par = ParametricRegion[{us + ts . w, restr}, Evaluate@Join[ts, us] ];
    xs = Array[\[FormalX], RegionDimension@par];
    With[{cond = Reduce[RegionMember[par, xs], xs, Reals]},
      ImplicitRegion[cond, Evaluate@xs]
    ]
  ];
ConicalSimplexHullRegion[reg_?RegionQ, w_List?MatrixQ] :=
  Null /; Message[ConicalSimplexHullRegion::dimerr, 
    RegionEmbeddingDimension[reg], Last[Dimensions@w,0] ];
ConicalSimplexHullRegion::dimerr = 
  "Embedding dimension `1` does not match with vector dimension `2`.";
SetAttributes[ConicalSimplexHullRegion, {Protected, ReadProtected}];


AcuteCone[{}] := {{}, {}};
AcuteCone[{{}}] := Message[AcuteCone::invgen];
AcuteCone[gen_?(MatrixQ[#, NumericQ] &)] :=
  Module[{aa, m, n, mf, t, bb, cc},
    aa = Union[gen];
    {m, n} = Dimensions[aa];
    mf = RegionMember@ParametricRegion[
      Evaluate@{Array[t, m].aa, And @@ Thread[Array[t, m] >= 0]},
      Evaluate@Array[t, m]
    ];
    cc = Select[aa, ! mf[-#] &];
    bb = If[Length[aa] == Length[cc], {},
      DeleteCases[RowReduce@Complement[aa, cc], {0 ..}]
    ];
    {bb, cc}
  ];
AcuteCone::invgen = "Invalid matrix of generators provided.";
SetAttributes[AcuteCone, {Protected, ReadProtected}];


DualCone[{}] := {};
DualCone[{{}}] := Null /; Message[DualCone::invgen];
DualCone[gen_?(MatrixQ[#, NumericQ] &)] :=
  Module[{aa, m, n, t, mf, gammaF, bb, cc},
    aa = Union[gen];
    {m, n} = Dimensions[aa];
    mf = RegionMember@ParametricRegion[
      Evaluate@{Array[t, m] . aa, And @@ Thread[Array[t, m] >= 0]},
      Evaluate@Array[t, m]
    ];
    gammaF[{vv_, ww_}, a_] :=
      Block[{vp, piv, inC, h, gg, orthI, z, Irel, Ipick},
      piv = If[Length@vv == 0, {},
        Position[vv.a, Except[0, _?NumericQ], {1}]
      ];
      inC = Not@mf[-a];
      If[Length@piv > 0,
        vp = vv[[First@First@piv]];
        Return[{
          Map[# - (a.#)/(a.vp) vp &, Delete[vv, First@piv] ],
          NormalizeGCD /@ Append[
            Map[# - (a.#)/(a.vp) vp &, ww], If[inC, -vp/(a.vp), Nothing]
          ]
        }]
      ];
      h = First@FirstPosition[aa, a];
      orthI = (Flatten@Position[Take[aa, UpTo@h].#, 0] &);
      gg = GroupBy[If[#.a == 0, #, #/Abs[#.a] ] & /@ ww, Sign[#.a] &];
      z = KeyMap[Total]@AssociationMap[
        Union[Intersection @@ orthI /@ #, {h}] &,
        Tuples@Lookup[gg, {1,-1}, {}]
      ];
      Irel = SimpleGraph@RelationGraph[
        ContainsAll[#2, #1] &, Values@z, DirectedEdges -> True
      ];
      Ipick = Select[
        Pick[VertexList@Irel, VertexOutDegree@Irel, 0],
        NoneTrue[orthI /@ Lookup[gg, 0, {}], ContainsAll@#] &
      ];
      {vv, Join[
        Select[ww, #.a == 0 || (inC && #.a < 0) &], 
        NormalizeGCD /@ Keys@Select[z, MatchQ[Alternatives@@Ipick] ]
      ]}
    ];
    {bb, cc} = Fold[gammaF, {IdentityMatrix[n], {}}, aa];
    Union[bb, -bb, cc]
  ];
DualCone::invgen = "Invalid matrix of generators provided.";


SyntaxInformation[FindNonSimplePaths] = {"ArgumentsPattern" -> {_,_,_,_}};
FindNonSimplePaths[e_?EdgeListQ, s_, t_, kspec_] :=
  FindNonSimplePaths[Graph[e], s, t, kspec];
FindNonSimplePaths[g_Graph, s_, t_, kmax_Integer] :=
  FindNonSimplePaths[g, s, t, {1, kmax}] /; AllTrue[{s, t}, VertexQ[g, #] &];
FindNonSimplePaths[g_Graph, s_, t_, {kmax_Integer}] :=
  FindNonSimplePaths[g, s, t, {kmax, kmax}] /; AllTrue[{s, t}, VertexQ[g, #] &];
FindNonSimplePaths[g_Graph, s_, t_, {kmin_Integer, kmax_Integer}] :=
  Module[{adj, dist, step},
    adj = GroupBy[EdgeList[g], First -> Last];
    dist = Association[(# -> GraphDistance[g, #, t] &) /@ VertexList@g];
    step[{m___, l_}] := (Join[{m, l}, {#}] &) /@
      Select[adj[l], (dist[#] + Length[{m}] <= kmax &)];
    Cases[
      Join @@ NestList[ Apply[Join]@*Map[step], {{s}}, Max[1, kmax] ],
      x:{s, ___, t} /; (kmin <= Length[x] - 1 <= kmax)
    ]
  ] /; AllTrue[{s, t}, VertexQ[g, #] &];
FindNonSimplePaths[g_, _, _, _] := 
  Null /; Message[FindNonSimplePaths::invgraph, g];
FindNonSimplePaths[g_Graph, s_, t_, _] /; (!VertexQ[g,s]) := 
  Null /; Message[FindNonSimplePaths::invvertex, s, EdgeList@g];
FindNonSimplePaths[g_Graph, s_, t_, _] /; (!VertexQ[g,t]) :=
  Null /; Message[FindNonSimplePaths::invvertex, t, EdgeList@g];
FindNonSimplePaths::invgraph = "The argument `1` is not a valid graph.";
FindNonSimplePaths::invvertex = "The argument `1` is not a valid vertex of `2`.";
SetAttributes[FindNonSimplePaths, {Protected, ReadProtected}];


SyntaxInformation[SolveMatrixLeft] = {"ArgumentsPattern" -> {_,_}};
SolveMatrixLeft[a_?MatrixQ, b_?MatrixQ] :=
  Module[{dimA, dimB, err, res},
    {dimA, dimB} = Dimensions /@ {a, b};
    If[ dimA[[2]] != dimB[[2]], 
      Message[SolveMatrixLeft::lslc];Return[$Failed]
    ];
    {err, res} = ReapMessages[
      (Check[LinearSolve[Transpose[a], #1], $Failed] &) /@ b
    ];
    If[err =!= {},
      Message[SolveMatrixLeft::err];Return[$Failed],
      Return[res]
    ]
  ];
SolveMatrixLeft[a_, b_] := Null /; Message[SolveMatrixLeft::argx];
SolveMatrixLeft::lslc = "Coefficient matrix and target matrix do not have matching dimensions.";
SolveMatrixLeft::err = "An error occured while solving the system.";
SolveMatrixLeft::argx = "Arguments provided are not matrices.";
SetAttributes[SolveMatrixLeft, {Protected, ReadProtected}];


SyntaxInformation[ReapMessages] = {"ArgumentsPattern" -> {_}};
ReapMessages[eval_] :=
  Module[{msgs, res},
    msgs = {};
    Internal`InheritedBlock[{Message, $InMsg},
      $InMsg = False;
      Unprotect[Message];
      Message[msg_, vars___] /; !$InMsg :=
        Block[{$InMsg = True},
          AppendTo[msgs, {HoldForm[msg], vars}];
          Message[msg, vars]
        ];
      res = eval
    ];
    Return[{msgs, res}];
  ];
SetAttributes[ReapMessages, {HoldFirst, Protected, ReadProtected}];


SyntaxInformation[EchoUniqueMessages] = {"ArgumentsPattern" -> {_}};
EchoUniqueMessages[eval_] :=
  Module[{msgs, res, uniqueMsgs},
    {msgs, res} = Quiet@ReapMessages[eval];
    uniqueMsgs = UniqueCases[msgs, {HoldForm[_MessageName], ___}];
    Map[Apply[HoldForm@*Message], uniqueMsgs] // ReplaceAll[
      HoldForm[ Message[HoldForm[m_], v___] ] :> 
      HoldForm[ Message[m, v] ]
    ] // ReleaseHold;
    Return[res];
  ]
SetAttributes[EchoUniqueMessages, {HoldFirst, Protected, ReadProtected}];


SyntaxInformation[UsageForm] = {"ArgumentsPattern" -> {_, _.}};
UsageForm[u: {__String}, a: ({__String} | HoldPattern[Alternatives][__String] | Automatic): Automatic] := 
  Map[UsageForm[#, a] &, u];
UsageForm[u_String, a: ({__String} | HoldPattern[Alternatives][__String] | Automatic): Automatic] :=
  Module[{uf, handleV, TIrule, funcPatt, varPatt, vars},
    Attributes[uf] = {HoldFirst};
    uf[patt_] := ToString[Unevaluated[patt], StandardForm];
    funcPatt = (WordBoundary ~~ Pattern[#1, WordCharacter ..] ~~ 
      Pattern[#2, ("[" ~~ Shortest[__] ~~ "]&" | "] &" | "]") ..]) &;
    vars = If[a =!= Automatic, a,
      Flatten@StringCases[u,
        funcPatt[foo, args] :> StringSplit[args, ("["|"]"|",")] 
      ] 
    ] // DeleteDuplicates@*Flatten //
      (StringCases[#, WordBoundary ~~ WordCharacter .. ~~ WordBoundary] &) // 
      DeleteCases[_?(StringMatchQ[DigitCharacter ..])];
    varPatt = (WordBoundary ~~ Pattern[#, __] ~~ WordBoundary /;
      StringMatchQ[#, Alternatives @@ vars]) &;
    TIrule = (varPatt[vv] :> StringJoin["Style[", vv, ",\"TI\"]"]);
    handleV[x__] := ReleaseHold@Map[uf, ToExpression[
      StringReplace[StringJoin[x], TIrule], 
      StandardForm, Hold], {1}];
    StringReplace[u, {
      q : funcPatt[foo, args] :> handleV[q],
      varPatt[arg] :> handleV["Style[", arg, ",\"TI\"]"]
    }]
  ];
SetAttributes[UsageForm, {Protected, ReadProtected}];


End[]


EndPackage[]
