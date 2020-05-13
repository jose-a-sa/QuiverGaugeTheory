(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Main`"]


Unprotect["QuiverGaugeTheory`Main`*"];
ClearAll["QuiverGaugeTheory`Main`*"];


Map[(MessageName[#, "usage"] = "") &,
  ToExpression[{"\[Alpha]", "\[Beta]", "\[Gamma]", "\[Delta]", "\[Epsilon]",
    "\[Zeta]", "\[Eta]", "\[Theta]", "\[Iota]", "\[Kappa]", "\[Lambda]",
    "\[Mu]", "\[Nu]", "\[Xi]", "\[Omicron]", "\[Rho]", "\[Sigma]",
    "\[Tau]", "\[Upsilon]", "\[Phi]", "\[Chi]", "\[Psi]", "\[Omega]"},
  InputForm, Hold], {2}]; // ReleaseHold

X::usage = "";
U::usage = "";


FieldsInPotential::usage = "";


FTerms::usage = "";


FTermsConstraint::usage = "";


FTermsTable::usage = "";


ChangeGroupIndices::usage = "";


PotentialCoefficientTestQ::usage = "";


PotentialQ::usage = "";


ToricPotentialQ::usage = "\
\!\(\*RowBox[{\"ToricPotentialQ\", \"[\", StyleBox[\"W\", \"TI\"], \"]\"}]\) \
yields True if the F-terms for the superpotential \!\(\*StyleBox[\"W\", \"TI\"]\) result in \
exactly 2 monominals with opposite coefficients \[PlusMinus]1.";


Begin["`Private`"]


SyntaxInformation[FieldsInPotential] = {"ArgumentsPattern" -> {_, _.}};

FieldsInPotential[W_] := Cases[
  Expand@W, Subscript[X, _][__], Infinity
] // DeleteDuplicates // Sort;


SyntaxInformation[FTerms] = {"ArgumentsPattern" -> {_, _.}};

FTerms[W_, f_: Identity] :=
  Expand@Collect[Expand@D[W, {FieldsInPotential@W}], Subscript[X, _][__] .., f@*Simplify];


SyntaxInformation[FTermsConstraint] = {"ArgumentsPattern" -> {_, _., _.}};

FTermsConstraint[W_, f_: Identity, g_: Plus] := 
  g @@@ ReplaceAll[List @@@ FTerms[W, f], Subscript[X, _][__] -> 1];


SyntaxInformation[FTermsTable] = {"ArgumentsPattern" -> {_}};

FTermsTable[W_] := 
  Grid[Transpose[{
    FTerms[W, Highlighted],
    Simplify@FTermsConstraint[W], 
    Simplify@FTermsConstraint[W, Abs]
  }], Frame -> All];


SyntaxInformation[PotentialCoefficientTestQ] = {"ArgumentsPattern" -> {_, _.}};

PotentialCoefficientTestQ[coefPatt_] := 
  PotentialCoefficientTestQ[#, coefPatt] &;
PotentialCoefficientTestQ[W_, coefPatt_] := MatchQ[Expand@W,
  HoldPattern[Plus][(HoldPattern[Times][coefPatt, Subscript[X, _][__] ..] |
  HoldPattern[Times][Subscript[X, _][__] ..]) ..]
];


SyntaxInformation[PotentialQ] = {"ArgumentsPattern" -> {_}};

PotentialQ[W_] := PotentialCoefficientTestQ[__][Expand@W];


SyntaxInformation[ToricPotentialQ] = {"ArgumentsPattern" -> {_}};

ToricPotentialQ[W_] := 
  Simplify@And[
    And @@ Thread[FTermsConstraint[W] == 0],
    And @@ Thread[FTermsConstraint[W, Abs] == 2]
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
    MatchQ[symb, X | \[Alpha] | \[Beta] | \[Gamma] | \[Delta] | \[Epsilon] | \[Zeta] |
      \[Eta] | \[Theta] | \[Iota] | \[Kappa] | \[Lambda] | \[Mu] | \[Nu] |
      \[Xi] | \[Omicron] | \[Rho] | \[Sigma] | \[Tau] | \[Upsilon] | \[Phi] |
      \[Chi] | \[Psi] | \[Omega] ];


With[{syms = Names["QuiverGaugeTheory`Main`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[]


EndPackage[]
