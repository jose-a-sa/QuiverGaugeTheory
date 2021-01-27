(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Core`", {
  "QuiverGaugeTheory`Tools`"
}]


$RedefinitionVars = Alternatives@@
  ToExpression@CharacterRange["\[FormalAlpha]", "\[FormalOmega]"];


X::usage = "";
Untrace::usage = "";
Fields::usage = "";
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
FEquationsTrivialQ::usage = "";
ToricPotentialQ::usage = "\
ToricPotentialQ[W] yields True if the F-terms for the superpotential W result\ 
in exactly 2 monominals with opposite coefficients \[PlusMinus]1.";
ToricPotentialTeXForm::usage = "";


Begin["`Private`"]


SyntaxInformation[X] = {"ArgumentsPattern" -> {_, _, _.}};
X[i_Integer, j_Integer, k_Integer : 1] := Subscript[X, k][i, j]


SyntaxInformation[FieldQ] = {"ArgumentsPattern" -> {_}};
FieldQ[ Subscript[X, _][_, _] ] := True;
FieldQ[_] := False;


SyntaxInformation[FieldPowerQ] = {"ArgumentsPattern" -> {_}};
FieldPowerQ[ Power[_?FieldQ, _.] ] := True;
FieldPowerQ[ (_?FieldQ) ] := True;
FieldPowerQ[_] := False;


SyntaxInformation[AbelianFieldProductQ] = {"ArgumentsPattern" -> {_}};
AbelianFieldProductQ[ HoldPattern[Times][__?FieldPowerQ] ] := True;
AbelianFieldProductQ[_] := False;


SyntaxInformation[NonAbelianFieldProductQ] = {"ArgumentsPattern" -> {_}};
NonAbelianFieldProductQ[ HoldPattern[CenterDot][__?FieldPowerQ] ] := True;
NonAbelianFieldProductQ[_] := False;


SyntaxInformation[FieldProductQ] = {"ArgumentsPattern" -> {_}};
FieldProductQ[_?AbelianFieldProductQ] := True;
FieldProductQ[_?NonAbelianFieldProductQ] := True;
FieldProductQ[_] := False;


SyntaxInformation[AbelianQ] = {"ArgumentsPattern" -> {_}};
AbelianQ[x_] := FreeQ[ExpandAll@x, _?NonAbelianFieldProductQ];


SyntaxInformation[Fields] = {"ArgumentsPattern" -> {_}};
Fields[W_] := Sort@UniqueCases[ ExpandAll@W, _?FieldQ ];


SyntaxInformation[FieldProducts] = {"ArgumentsPattern" -> {_}};
FieldProducts[W_] := DeleteDuplicates@Map[
  ReplaceAll[HoldPattern[Times][l___, _?(FreeQ[_?FieldQ]), r___] :> l*r], 
  UniqueCases[{ExpandAll@W}, _?FieldProductQ | HoldPattern[Times][_, _?FieldProductQ] ]
];


SyntaxInformation[Abelianize] = {"ArgumentsPattern" -> {_}}
Abelianize::warn = "Abelianization of the fields was done."
Abelianize[x_] := ReplaceAll[CenterDot -> Times]@x;


CenterDot[l___, a_ + b_, r___] := CenterDot[l, a, r] + CenterDot[l, b, r]
CenterDot[l___, a_*c_, r___] := c CenterDot[l, a, r] /; (FreeQ[c, _?FieldQ])
CenterDot[l___, c : Except[Untrace], r___] := c CenterDot[l, r] /; (FreeQ[c, _?FieldQ])
CenterDot[l___, Untrace, r___] := CenterDot[r, l]
CenterDot[l___, a_^p_., a_^q_., r___] := CenterDot[l, a^(p + q), r]
CenterDot[x_] := x
CenterDot[ Sequence[] ] := 1
SetAttributes[CenterDot, {Flat, OneIdentity}]
Default[CenterDot] = Default[Times];
Untrace /: Times[l___, Untrace, r___] := Times[l, 1, r];


SetAttributes[NonCommutativeMultiply, {Flat, Listable, OneIdentity}]
NonCommutativeMultiply[x___] := CenterDot[x];
Default[NonCommutativeMultiply] = Default[Times];


SyntaxInformation[DG] = {"ArgumentsPattern" -> {_, _, _.}};
DG[{x__}, var__] := Map[DG[#, var] &, {x}];
DG[any_, {{vars__?FieldQ}}] := Map[DG[any, #] &, {vars}];
DG[any_, vars : ({_, _Integer?Positive} ..)] := 
 Fold[DG, any, Flatten[ConstantArray @@@ {vars}] ];
DG[any_, vars__] := Fold[DG, any, {vars}]
DG[HoldPattern[Plus][x__], var_?FieldQ] :=
  Total@Map[DG[#, var] &, {x}];
DG[HoldPattern[h : (CenterDot | Times)][x__], var_?FieldQ] :=
  Total@Array[h @@ MapAt[DG[#, var] &, {x}, {#}] &, Length@{x}];
DG[var_, var_?FieldQ] := Untrace;
DG[f_, var_?FieldQ] := D[f, var];


SyntaxInformation[PotentialCoefficientTestQ] = {"ArgumentsPattern" -> {_, _.}};
PotentialCoefficientTestQ[coefPatt_] := 
  PotentialCoefficientTestQ[#, coefPatt] &;
PotentialCoefficientTestQ[W_, coefPatt_] := MatchQ[ExpandAll@W,
  HoldPattern[Plus][Alternatives[
    (HoldPattern[Times][coefPatt, __?FieldPowerQ] | _?AbelianFieldProductQ) ..,
    (HoldPattern[Times][coefPatt, _?NonAbelianFieldProductQ] | _?NonAbelianFieldProductQ) ..] 
  ]
];


SyntaxInformation[PotentialQ] = {"ArgumentsPattern" -> {_}};
PotentialQ[W_] := PotentialCoefficientTestQ[__][ExpandAll@W];


SyntaxInformation[AbelianPotentialQ] = {"ArgumentsPattern" -> {_}};
AbelianPotentialQ[W_?PotentialQ] := AbelianQ@W;
AbelianPotentialQ[_] := False;


SyntaxInformation[NonAbelianPotentialQ] = {"ArgumentsPattern" -> {_}};
NonAbelianPotentialQ[W_?PotentialQ] := Not@AbelianQ@W;
NonAbelianPotentialQ[_] := False;


SyntaxInformation[FTerms] = {"ArgumentsPattern" -> {_, _.}};
FTerms[W_?PotentialQ, f_: Identity] := ExpandAll@Collect[
  ExpandAll@DG[W, {Fields@W}], 
    _?FieldProductQ | HoldPattern[Times][_., (__?FieldPowerQ)], 
  f@*Simplify
];


SyntaxInformation[FTermsConstraint] = {"ArgumentsPattern" -> {_, _., _.}};
FTermsConstraint[W_?PotentialQ, f_: Identity, g_: Plus] := 
  g @@@ ReplaceAll[List @@@ FTerms[W, f], (_?FieldQ) -> 1];


SyntaxInformation[FTermsTable] = {"ArgumentsPattern" -> {_}};
FTermsTable[W_?PotentialQ] := 
  Grid[Transpose[{
    Fields@W,
    FTerms[W, Highlighted],
    Simplify@FTermsConstraint[W], 
    Simplify@FTermsConstraint[W, Abs]
  }], Frame -> All];


SyntaxInformation[ToricPotentialQ] = {"ArgumentsPattern" -> {_}};
ToricPotentialQ[W_?PotentialQ] := 
  Simplify@And[
    And @@ Thread[FTermsConstraint[W] == 0],
    SameQ @@ FTermsConstraint[W, Abs]
  ];
ToricPotentialQ[_] := False


SyntaxInformation[FEquationsTrivialQ] = {"ArgumentsPattern" -> {_, _.}};
FEquationsTrivialQ[W_?PotentialQ][diff_] := 
  FEquationsTrivialQ[diff, W];
FEquationsTrivialQ[diff_, W_?PotentialQ] :=
  Module[{grB, vars},
    Message[Abelianize::warn];
    vars = Fields@W;
    grB = GroebnerBasis[FTerms@Abelianize@W, vars];
    PossibleZeroQ@Last@PolynomialReduce[Abelianize@diff, grB, vars]
  ];


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


SyntaxInformation[ToricPotentialTeXForm] = {"ArgumentsPattern" -> {_, _.}};
ToricPotentialTeXForm[W_?ToricPotentialQ, perline : (_Integer?NonNegative) : 3] := 
  Module[{texStr, terms, gather, sorted, sortF},
    sortF = Composition[
      StringRiffle,
      ApplyAt[("X_{"<>#1<>If[StringLength[#1<>#2]>2,",",""]<>#2<>"}"<>#3 &), {1}],
      First,
      FindCycle[#, Infinity, All] &,
      StringCases["X_{" ~~ (x : DigitCharacter ..) ~~ ("" | ",") ~~ 
          (y : DigitCharacter ..) ~~ "}" ~~ (z : "" | ("^" ~~ (DigitCharacter ..))) :> 
        DirectedEdge[x, y, z]
      ]
    ];
    texStr = ToString[ W /. {Subscript[X, k_][i_, j_] :> 
        If[ FreeQ[W, Subscript[X, 2][i, j] ], Subscript[X, Row[{i, j}] ],
          Subsuperscript[ X, Row[{i, j}], Row[{k}] ] ]}, TeXForm];
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


End[]


EndPackage[]
