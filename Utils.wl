(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Utils`"]


ApplyAt::usage = "";
FirstLast::usage = "";
SelectDelete::usage = "";
EdgeListQ::usage = "";
KeysByValueLength::usage = "";
MinMaxExponent::usage = "";
CyclicRange::usage = "";
CyclicPatternSequence::usage = "";
ToCyclicPattern::usage = "";
ToSubtractList::usage = "";
NormalizeGCD::usage = "";
CollinearQ::usage = "";
StrictlyCollinearQ::usage = "";
CoplanarQ::usage = "";
StrictlyCoplanarQ::usage = "";
UniqueCases::usage = "";
IndexedList::usage = "";
GridRulesGraphics::usage = "";

FindNonSimplePaths::usage = "";
SolveMatrixLeft::usage = "";

UsageForm::usage = "";
ReapMessages::usage = "";
EchoUniqueMessages::usage = "";


Begin["`Private`"]


SyntaxInformation[ApplyAt] = {"ArgumentsPattern" -> {_, _.}};
ApplyAt[f_, levelspec_ : {0}] := 
  Apply[f, #, levelspec] &;


SyntaxInformation[FirstLast] = {"ArgumentsPattern" -> {_}};
FirstLast[expr_] := {First@expr,Last@expr};


SyntaxInformation[SelectDelete] = {"ArgumentsPattern" -> {_,_.,_.}};
SelectDelete[crit_][list_] := SelectDelete[list, crit];
SelectDelete[list_, crit_, n_ : Infinity] :=
  {Select[list, crit, n], Select[list, Not@*crit, n]};


SyntaxInformation[EdgeListQ] = {"ArgumentsPattern" -> {_}};
EdgeListQ[expr_] := 
  MatchQ[expr, { (DirectedEdge[__]|UndirectedEdge[__]) .. }];


SyntaxInformation[KeysByValueLength] = {"ArgumentsPattern" -> {_}};
KeysByValueLength[a : KeyValuePattern[{}] ] :=
  KeyValueMap[Splice@Table[#1, Length@#2] &, Association@a];


SyntaxInformation[MinMaxExponent] = {"ArgumentsPattern" -> {_, _.}};
MinMaxExponent[patt_][expr_] := MinMaxExponent[expr, patt];
MinMaxExponent[expr_, patt_] := 
  MinMax@Exponent[
    MonomialList@ExpandAll[expr /. {x: patt :> \[FormalLambda] x}], 
    \[FormalLambda]
  ]


SyntaxInformation[CyclicRange] = {"ArgumentsPattern" -> {_, _., _., _.}};
CyclicRange[m_?Positive][i_Integer, f_Integer, s : _Integer?Positive : 1] := 
  CyclicRange[i, f, s, m]
CyclicRange[f_Integer, m_?Positive] := 
  CyclicRange[1, f, 1, m];
CyclicRange[i_Integer, f_Integer, m_Integer?Positive] :=
  CyclicRange[i, f, 1, m];
CyclicRange[i_Integer, f_Integer, s_Integer?Positive, m_Integer?Positive] := 
  ReplaceAll[0 -> m]@Mod[Range[i, i + Mod[f - i, m], s], m]


SyntaxInformation[CyclicPatternSequence] = {"ArgumentsPattern" -> {_.}};
CyclicPatternSequence[patt__] := Alternatives @@ Nest[
  RotateRight, PatternSequence[patt], Length[{patt}] - 1]
CyclicPatternSequence[] := PatternSequence[];


SyntaxInformation[ToCyclicPattern] = {"ArgumentsPattern" -> {_}};
ToCyclicPattern[ x_ ] := 
  Alternatives @@ NestList[RotateRight, x, Length@x -1]


SyntaxInformation[ToSubtractList] = {"ArgumentsPattern" -> {_}};
ToSubtractList[ expr : (List|And)[Except[_List]..] ] := 
  Map[ Through@*If[MatchQ[_Equal], Apply[Subtract], Identity],
    List @@ expr
  ];


SyntaxInformation[NormalizeGCD] = {"ArgumentsPattern" -> {_}};
NormalizeGCD[p: {0 ..}] := p; 
NormalizeGCD[p: {__?ExactNumberQ}] := p / (GCD @@ p);
NormalizeGCD[p: {__}] := p;


SyntaxInformation[CollinearQ] = {"ArgumentsPattern" -> {_}};
CollinearQ[pts_?MatrixQ] := 
  MatrixRank@Rest[(# - First@pts &) /@ pts] <= 1;
CollinearQ[expr_] := False;


SyntaxInformation[StrictlyCollinearQ] = {"ArgumentsPattern" -> {_}};
StrictlyCollinearQ[pts_?MatrixQ] := 
  MatrixRank@Rest[(# - First@pts &) /@ pts] == 1;
StrictlyCollinearQ[expr_] := False;


SyntaxInformation[CoplanarQ] = {"ArgumentsPattern" -> {_}};
CoplanarQ[pts_?MatrixQ] := 
  MatrixRank@Rest[(# - First@pts &) /@ pts] <= 2;
CollinearQ[expr_] := False;


SyntaxInformation[StrictlyCoplanarQ] = {"ArgumentsPattern" -> {_}};
StrictlyCoplanarQ[pts_?MatrixQ] := 
  MatrixRank@Rest[(# - First@pts &) /@ pts] == 2;
StrictlyCollinearQ[expr_] := False;


SyntaxInformation[UniqueCases] = SyntaxInformation[Cases];
UniqueCases[pattern_, opts : OptionsPattern[Cases] ][expr_] :=
  UniqueCases[expr, pattern, opts]
UniqueCases[expr_, pattern_, opts : OptionsPattern[Cases] ] :=
  DeleteDuplicates@Cases[expr, pattern, Infinity, opts]


SyntaxInformation[IndexedList] = {"ArgumentsPattern" -> {_, _., _.}};
IndexedList[l_List] := Transpose[{Range@Length@l, l}]
IndexedList[l_List, n0_] := 
  Transpose[{Range[n0, Length[l] + (n0 - 1)], l}]
IndexedList[l_List, n0_, di_] := 
  Transpose[{Range[n0, n0 + di (Length[l] - 1), di], l}]


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


SyntaxInformation[FindNonSimplePaths] = {"ArgumentsPattern" -> {_,_,_,_}};
FindNonSimplePaths::invgraph = "The argument `1` is not a valid graph.";
FindNonSimplePaths::invvertex = "The argument `1` is not a valid vertex of `2`.";
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
  Message[FindNonSimplePaths::invgraph, g];
FindNonSimplePaths[g_Graph, s_, t_, _] := 
  Message[FindNonSimplePaths::invvertex, s, EdgeList@g] /; (!VertexQ[g,s]);
FindNonSimplePaths[g_Graph, s_, t_, _] :=
  Message[FindNonSimplePaths::invvertex, t, EdgeList@g] /; (!VertexQ[g,t]);


SyntaxInformation[SolveMatrixLeft] = {"ArgumentsPattern" -> {_,_}};
SolveMatrixLeft::lslc = "Coefficient matrix and target matrix do not have matching dimensions.";
SolveMatrixLeft::err = "An error occured while solving the system.";
SolveMatrixLeft::argx = "Arguments provided are not matrices.";
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
SolveMatrixLeft[a_, b_] := Message[SolveMatrixLeft::argx];


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
  ]
SetAttributes[ReapMessages, HoldFirst]


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
SetAttributes[EchoUniqueMessages, {HoldFirst}]


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


End[]


EndPackage[]