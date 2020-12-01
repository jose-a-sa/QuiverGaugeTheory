(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Tools`"]


UsageForm::usage = "";
ApplyTo::usage = "";
UniqueCases::usage = "";
FirstLast::usage = "";
IndexedList::usage = "";
ColinearQ::usage = "";
CoplanarQ::usage = "";
NormalizeGCD::usage = "";
GridRulesGraphics::usage = "";
ToSubtractList::usage = "";
MinMaxExponent::usage = "";
EdgeListQ::usage = "";
FindPathWithCycles::usage = "";


Begin["`Private`"]


SyntaxInformation[FirstLast] = {"ArgumentsPattern" -> {_}};
FirstLast[expr_] := 
  {First@expr,Last@expr};


SyntaxInformation[EdgeListQ] = {"ArgumentsPattern" -> {_}};
EdgeListQ[expr_] := 
  MatchQ[expr, { (DirectedEdge[__]|UndirectedEdge[__]) .. }];


SyntaxInformation[MinMaxExponent] = {"ArgumentsPattern" -> {_, _.}};
MinMaxExponent[patt_][expr_] := MinMaxExponent[expr, patt];
MinMaxExponent[expr_, patt_] := MinMax@Exponent[
    MonomialList@Expand[expr /. {x: patt :> \[FormalLambda] x}], 
    \[FormalLambda]
  ]


SyntaxInformation[ToSubtractList] = {"ArgumentsPattern" -> {_}};
ToSubtractList[ expr : (List|And)[Except[_List]..] ] := 
  Map[ Through@*If[MatchQ[_Equal], Apply[Subtract], Identity],
    List @@ expr
  ];


SyntaxInformation[NormalizeGCD] = {"ArgumentsPattern" -> {_}};
NormalizeGCD[p: {0 ..}] := p; 
NormalizeGCD[p: {__?ExactNumberQ}] := p / (GCD @@ p);
NormalizeGCD[p: {__}] := p;


SyntaxInformation[ColinearQ] = {"ArgumentsPattern" -> {_}};
ColinearQ[pts_?MatrixQ] := 
  MatrixRank@Rest[(# - First@pts &) /@ pts] <= 1;
ColinearQ[expr_] := False;


SyntaxInformation[CoplanarQ] = {"ArgumentsPattern" -> {_}};
CoplanarQ[pts_?MatrixQ] := 
  MatrixRank@Rest[(# - First@pts &) /@ pts] <= 2;
ColinearQ[expr_] := False;


SyntaxInformation[ApplyTo] = {"ArgumentsPattern" -> {_, _.}};
ApplyTo[f_, levelspec_ : {0}] := 
  Apply[f, #, levelspec] &;


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



SyntaxInformation[FindPathWithCycles] = {"ArgumentsPattern" -> {_,_,_,_}};
FindPathWithCycles[edges_?EdgeListQ, s_, t_, k_Integer?Positive] :=
  FindPathWithCycles[edges, s, t, {1, k}];
FindPathWithCycles[edges_?EdgeListQ, s_, t_, {k_Integer?Positive}] :=
  FindPathWithCycles[edges, s, t, {k, k}];
FindPathWithCycles[edges_?EdgeListQ, s_, t_, 
  {kmin_Integer?NonNegative, kmax_Integer?NonNegative}] :=
    Module[{paths, cyc, combos},
      cyc = GroupBy[FindCycle[edges, kmax - 1, All], 
        Length -> ({Last[Last@#1] -> Splice@Join[First /@ #1, {Last@Last@#1}]} &)];
      paths = GroupBy[FindPath[edges, s, t, {Min[kmin, kmax - Max@Keys@cyc], kmax}, All], 
        (Length[#] - 1 &)];
      combos = Select[Tuples[{Keys@paths, Keys@cyc}], kmin <= Total[#] <= kmax &];
      DeleteDuplicates@DeleteCases[{}]@Join[
        Join @@ Values@KeySelect[paths, kmin <= # <= kmax &], 
        Join @@ MapThread[
            Table[DeleteCases[p /. cyc[#2], p], {p, paths[#1]}] &, 
          Transpose@combos]
      ]
    ]


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
      ] ] // DeleteDuplicates@*Flatten //
      (StringCases[#, WordBoundary ~~ WordCharacter .. ~~ WordBoundary] &) // 
      DeleteCases[_?(StringMatchQ[DigitCharacter ..])];
    varPatt = (WordBoundary ~~ Pattern[#, __] ~~ WordBoundary /;
      StringMatchQ[#, Alternatives @@ vars]) &;
    TIrule = (varPatt[vv] :> StringJoin["Style[", vv, ",\"TI\"]"]);
    handleV = (ReleaseHold@Map[uf, ToExpression[
      StringReplace[StringJoin[##], TIrule], 
      StandardForm, Hold], {1}
    ] &);
    StringReplace[u, {
      q : funcPatt[foo, args] :> handleV[q],
      varPatt[arg] :> handleV["Style[", arg, ",\"TI\"]"]
    }]
  ];


End[]


EndPackage[]