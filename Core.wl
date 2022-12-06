(* ::Package:: *)

Unprotect["QuiverGaugeTheory`Core`*"];
ClearAll["QuiverGaugeTheory`Core`*"];


BeginPackage["QuiverGaugeTheory`Core`", {
  "QuiverGaugeTheory`Utils`"
}]


$RedefinitionVars = Alternatives@@
  ToExpression@CharacterRange["\[FormalAlpha]", "\[FormalOmega]"];


X::usage = "";
Untrace::usage = "";
FieldCases::usage = "";
FieldQ::usage = "";
FieldPowerQ::usage = "";
FieldProducts::usage = "";
FieldProductQ::usage = "";
AbelianFieldProductQ::usage = "";
NonAbelianFieldProductQ::usage = "";
AbelianQ::usage = "";
Abelianize::usage = "";
DG::usage = "";
FTerms::usage = "";
FTermsConstraint::usage = "";
FTermsTable::usage = "";
ChangeGroupIndices::usage = "";
PotentialCoefficientTestQ::usage = "";
PotentialQ::usage = "";
AbelianPotentialQ::usage = "";
NonAbelianPotentialQ::usage = "";
ToricPotentialQ::usage = "";
PotentialMemberQ::usage = "";
IntegrateOutMassTerms::usage = "";
PotentialEulerCharacteristic::usage = "";
ToricPotentialTeXForm::usage = "";


Begin["`Private`"]


SyntaxInformation[X] = {"ArgumentsPattern" -> {_, _, _.}};
X[i_, j_, k_ : 1] := Subscript[X, k][i, j];
SetAttributes[X, {Protected, ReadProtected}];


SyntaxInformation[FieldQ] = {"ArgumentsPattern" -> {_}};
FieldQ[ Subscript[X, _][_, _] ] := True;
FieldQ[_] := False;
SetAttributes[FieldQ, {Protected, ReadProtected}];


SyntaxInformation[FieldPowerQ] = {"ArgumentsPattern" -> {_}};
FieldPowerQ[ Power[_?FieldQ, _.] ] := True;
FieldPowerQ[ (_?FieldQ) ] := True;
FieldPowerQ[_] := False;
SetAttributes[FieldPowerQ, {Protected, ReadProtected}];


SyntaxInformation[AbelianFieldProductQ] = {"ArgumentsPattern" -> {_}};
AbelianFieldProductQ[ HoldPattern[Times][__?FieldPowerQ] ] := True;
AbelianFieldProductQ[_] := False;
SetAttributes[AbelianFieldProductQ, {Protected, ReadProtected}];


SyntaxInformation[NonAbelianFieldProductQ] = {"ArgumentsPattern" -> {_}};
NonAbelianFieldProductQ[ HoldPattern[CenterDot][__?FieldPowerQ] ] := True;
NonAbelianFieldProductQ[_] := False;
SetAttributes[NonAbelianFieldProductQ, {Protected, ReadProtected}];


SyntaxInformation[FieldProductQ] = {"ArgumentsPattern" -> {_}};
FieldProductQ[_?AbelianFieldProductQ] := True;
FieldProductQ[_?NonAbelianFieldProductQ] := True;
FieldProductQ[_] := False;
SetAttributes[FieldProductQ, {Protected, ReadProtected}];


SyntaxInformation[AbelianQ] = {"ArgumentsPattern" -> {_}};
AbelianQ[x_] := FreeQ[ExpandAll@x, _?NonAbelianFieldProductQ];
SetAttributes[AbelianQ, {Protected, ReadProtected}];


SyntaxInformation[FieldCases] = {"ArgumentsPattern" -> {_}};
FieldCases[w_] := SortBy[
  UniqueCases[ ExpandAll@w, _?FieldQ ],
  Apply[DirectedEdge]
];
SetAttributes[FieldCases, {Protected, ReadProtected}];


SyntaxInformation[FieldProducts] = {"ArgumentsPattern" -> {_}};
FieldProducts[w_] := DeleteDuplicates@Map[
  ReplaceAll[HoldPattern[Times][l___, _?(FreeQ[_?FieldQ]), r___] :> l*r], 
  UniqueCases[{ExpandAll@w}, _?FieldProductQ | HoldPattern[Times][_, _?FieldProductQ] ]
];
SetAttributes[FieldProducts, {Protected, ReadProtected}];


SyntaxInformation[Abelianize] = {"ArgumentsPattern" -> {_}}
Abelianize[x_] := ReplaceAll[CenterDot -> Times]@x;
Abelianize::warn = "Abelianization of the fields was done."
SetAttributes[Abelianize, {Protected, ReadProtected}];


CenterDot[l___, a_ + b_, r___] := CenterDot[l, a, r] + CenterDot[l, b, r]
CenterDot[l___, a_*c_, r___] := c CenterDot[l, a, r] /; (FreeQ[c, _?FieldQ])
CenterDot[l___, c : Except[Untrace], r___] := c CenterDot[l, r] /; (FreeQ[c, _?FieldQ])
CenterDot[l___, Untrace, r___] := CenterDot[r, l]
(* CenterDot[l___, a_^p_., a_^q_., r___] := CenterDot[l, a^(p + q), r] *)
CenterDot[x_] := x
CenterDot[ Sequence[] ] := 1
Default[CenterDot] = Default[Times];
SetAttributes[CenterDot, {Flat, OneIdentity, Protected, ReadProtected}];
Untrace /: Times[l___, Untrace, r___] := Times[l, 1, r];


SyntaxInformation[DG] = {"ArgumentsPattern" -> {_, _, _.}};
DG[{x__}, var__] := 
  Map[DG[#, var] &, {x}];
DG[any_, {{vars__?FieldQ}}] := 
  Map[DG[any, #] &, {vars}];
DG[any_, vars : ({_, _Integer?Positive} ..)] := 
 Fold[DG, any, Flatten[ConstantArray @@@ {vars}] ];
DG[any_, vars__] := 
  Fold[DG, any, {vars}]
DG[HoldPattern[Plus][x__], var_?FieldQ] :=
  Total@Map[DG[#, var] &, {x}];
DG[HoldPattern[h : (CenterDot | Times)][x__], var_?FieldQ] :=
  Total@Array[h @@ MapAt[DG[#, var] &, {x}, {#}] &, Length@{x}];
DG[var_, var_?FieldQ] := 
  Untrace;
DG[f_, var_?FieldQ] := 
  D[f, var];
SetAttributes[DG, {Protected, ReadProtected}];

 
SyntaxInformation[PotentialCoefficientTestQ] = {"ArgumentsPattern" -> {_, _.}};
PotentialCoefficientTestQ[coefPatt_] := 
  PotentialCoefficientTestQ[#, coefPatt] &;
PotentialCoefficientTestQ[w_, coefPatt_] := MatchQ[ExpandAll@w,
  HoldPattern[Plus][Alternatives[
    (HoldPattern[Times][coefPatt, __?FieldPowerQ] | _?AbelianFieldProductQ) ..,
    (HoldPattern[Times][coefPatt, _?NonAbelianFieldProductQ] | _?NonAbelianFieldProductQ) ..] 
  ]
];
SetAttributes[PotentialCoefficientTestQ, {Protected, ReadProtected}];


SyntaxInformation[PotentialQ] = {"ArgumentsPattern" -> {_}};
PotentialQ[w_] := PotentialCoefficientTestQ[__][ExpandAll@w];
SetAttributes[PotentialQ, {Protected, ReadProtected}];


SyntaxInformation[AbelianPotentialQ] = {"ArgumentsPattern" -> {_}};
AbelianPotentialQ[w_?PotentialQ] := AbelianQ@w;
AbelianPotentialQ[_] := False;
SetAttributes[AbelianPotentialQ, {Protected, ReadProtected}];


SyntaxInformation[NonAbelianPotentialQ] = {"ArgumentsPattern" -> {_}};
NonAbelianPotentialQ[w_?PotentialQ] := Not@AbelianQ@w;
NonAbelianPotentialQ[_] := False;
SetAttributes[NonAbelianPotentialQ, {Protected, ReadProtected}];


SyntaxInformation[FTerms] = {"ArgumentsPattern" -> {_, _.}};
FTerms[w_?PotentialQ, f_: Identity] := 
  ExpandAll@Collect[
    ExpandAll@DG[w, {FieldCases@w}], 
    (_?FieldProductQ) | (_?FieldQ), 
    f@*Simplify
  ];
SetAttributes[FTerms, {Protected, ReadProtected}];


SyntaxInformation[FTermsConstraint] = {"ArgumentsPattern" -> {_, _., _.}};
FTermsConstraint[w_?PotentialQ, f_: Identity, g_: Plus] := 
  Module[{ff, gg},
    Map[ Replace[p_Plus :> gg@@p], 
      Expand@ReplaceAll[_?FieldQ->1]@FTerms[w, ff] 
    ] // ReplaceAll[{ff -> f, gg -> g}]
  ];
SetAttributes[FTermsConstraint, {Protected, ReadProtected}];


SyntaxInformation[FTermsTable] = {"ArgumentsPattern" -> {_}};
FTermsTable[w_?PotentialQ] := 
  Grid[Transpose[{
    FieldCases@w,
    FTerms[w, Highlighted],
    Simplify@FTermsConstraint[w], 
    Simplify@FTermsConstraint[w, Abs]
  }], Frame -> All];
SetAttributes[FTermsTable, {Protected, ReadProtected}];


SyntaxInformation[ToricPotentialQ] = {"ArgumentsPattern" -> {_}};
ToricPotentialQ[w_?PotentialQ] := 
  Simplify@And[
    And @@ Thread[FTermsConstraint[w] == 0],
    SameQ @@ FTermsConstraint[w, Abs]
  ];
ToricPotentialQ[_] := False
SetAttributes[ToricPotentialQ, {Protected, ReadProtected}];


PotentialMemberQ[w_?PotentialQ, c : {__DirectedEdge}, 0] :=
  AnyTrue[Map[DirectedEdge @@@ List @@ #&, FieldProducts@w], ContainsExactly@c];
PotentialMemberQ[w_?PotentialQ, c_?FieldProductQ, 0] :=
  MemberQ[Simplify @ FieldProducts@w, Simplify@c];
PotentialMemberQ[w_?PotentialQ, e_DirectedEdge, 1] :=
  MemberQ[Values@FieldCases@w, e];
PotentialMemberQ[w_?PotentialQ, e_?FieldQ, 1] :=
  MemberQ[Keys@FieldCases@w, e];
PotentialMemberQ[w_?PotentialQ, v_, 2] :=
  MemberQ[Flatten[List @@@ FieldCases@w], v];
PotentialMemberQ[w : Except[_?PotentialQ], _, _] :=
  Null /; Message[PotentialMemberQ::warg, w];
PotentialMemberQ[_?PotentialQ, x : Except[{__DirectedEdge} | _?FieldProductQ], 0] :=
  Null /; Message[PotentialMemberQ::fparg, x];
PotentialMemberQ[_?PotentialQ, x : Except[_DirectedEdge | _?FieldQ], 1] :=
  Null /; Message[PotentialMemberQ::earg, x];
PotentialMemberQ[_, _, _] := 
  False;
PotentialMemberQ::warg = "Argument `1` is not a valid potential.";
PotentialMemberQ::fparg = "Argument `1` is not a valid superpotential cycle.";
PotentialMemberQ::earg = "Argument `1` is not a valid superpotential edge or field.";
SetAttributes[PotentialMemberQ, {Protected, ReadProtected}];


SyntaxInformation[IntegrateOutMassTerms] = {"ArgumentsPattern" -> {_}};
IntegrateOutMassTerms[w_?PotentialQ] :=
  Module[{massF, int},
    massF = Select[FieldProducts@#, EqualTo[2]@*Length] &;
    int = NestWhile[
      # /. Last@Solve[0 == DG[#, {FieldCases@First@massF@#}], FieldCases@First@massF@#] &,
      w, (Length@massF[#] > 0 &)
    ];
    Simplify@Expand[int]
  ];
SetAttributes[IntegrateOutMassTerms, {Protected, ReadProtected}];


PotentialEulerCharacteristic[w_?ToricPotentialQ] :=
  Module[{fd, fp, fc},
    fd = FieldCases[w];
    fp = FieldProducts[w];
    fc = Union@Flatten[List @@@ fd];
    Length[fp] - Length[fd] + Length[fc]
  ];
SetAttributes[PotentialEulerCharacteristic, {Protected, ReadProtected}];


SyntaxInformation[ChangeGroupIndices] = {"ArgumentsPattern" -> {_, ___}};
ChangeGroupIndices[list:{__Integer}] := 
  ChangeGroupIndices@Thread[Range@Length[list] -> list];
ChangeGroupIndices[rules : {__Rule} ..] :=
  With[{len = Max@Cases[{rules}, _Integer, Infinity]},
    ChangeGroupIndices[Range[len] -> Fold[ReplaceAll, Range[len], {rules}] // Thread]
  ];
ChangeGroupIndices[i_Integer, j_Integer] := 
  ChangeGroupIndices[{i->j,j->i}];
ChangeGroupIndices[{rules__Rule}] := 
  Subscript[symb_, c_][a_, b_] :> Subscript[symb, c] @@ ({a, b} /. {rules}) /; 
    MatchQ[symb, X | Alternatives@@$RedefinitionVars ];
SetAttributes[ChangeGroupIndices, {Protected, ReadProtected}];


SyntaxInformation[ToricPotentialTeXForm] = {"ArgumentsPattern" -> {_, _.}};
ToricPotentialTeXForm[w_?ToricPotentialQ, perline : (_Integer?NonNegative) : 3] := 
  Module[{texStr, terms, gather, sorted, sortF},
    sortF = Composition[
      StringRiffle,
      ApplyAt[("X_{"<>#1<>If[StringLength[#1<>#2]>2,",",""]<>#2<>"}"<>#3 &), {1}],
      First,
      FindCycle[#, Infinity, All] &,
      StringCases["X_{" ~~ (x : DigitCharacter ..) ~~ ("" | ",") ~~ 
          (y : DigitCharacter ..) ~~ "}" ~~ (z : "" | ("^" ~~ ((DigitCharacter|LetterCharacter) ..))) :> 
        DirectedEdge[x, y, z]
      ]
    ];
    texStr = ToString[ w /. {Subscript[X, 1][i_, j_] :> If[
        MatchQ[UniqueCases[w, Subscript[X, _Integer][i, j] ], {Subscript[X, 1][i, j]}], 
        Subscript[X, Row[{i, j}] ], Subsuperscript[ X, Row[{i, j}], Row[{1}] ] ],
      Subscript[X, k:Except[1] ][i_, j_] :> Subsuperscript[ X, Row[{i, j}], Row[{k}] ]
    }, TeXForm];
    terms = StringSplit[texStr, c : {"+", "-"} :> c] // 
      Partition[If[First[#] != "-", Prepend[#, "+"], #], 2] &;
    gather = SortBy[StringCount[Last[#], "X"] &] /@ 
      GatherBy[MapAt[sortF, terms, {All, 2}], First];
    sorted = (StringJoin[" ", #1, " ", #2] &) @@@ 
      Join @@ Reverse@SortBy[First@*First]@gather;
    "&= " <> StringReplace[ StringJoin @@ 
        Riffle[sorted, " \\\\ \n & \\qquad", perline + 1], 
      StartOfLine ~~ " + " -> ""]
  ];
SetAttributes[ToricPotentialTeXForm, {Protected, ReadProtected}];


End[]


EndPackage[]
