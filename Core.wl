(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Core`", {
  "QuiverGaugeTheory`Tools`"
}]


$RedefinitionVars = Alternatives@@
  ToExpression@CharacterRange["\[FormalAlpha]", "\[FormalOmega]"];


X::usage = "";
Fields::usage = "";
FTerms::usage = "";
FTermsConstraint::usage = "";
FTermsTable::usage = "";
ChangeGroupIndices::usage = "";
PotentialCoefficientTestQ::usage = "";
PotentialQ::usage = "";
FEquationsTrivialQ::usage = "";
ToricPotentialQ::usage = "\
ToricPotentialQ[W] yields True if the F-terms for the superpotential W result\ 
in exactly 2 monominals with opposite coefficients \[PlusMinus]1.";
ToricPotentialTeXForm::usage = "";


Begin["`Private`"]


SyntaxInformation[X] = {"ArgumentsPattern" -> {_, _, _.}};
X[i_Integer, j_Integer, k_Integer : 1] := Subscript[X, k][i, j]


SyntaxInformation[Fields] = {"ArgumentsPattern" -> {_, _.}};
Fields[W_] := Sort@UniqueCases[ Expand@W, Subscript[X, _][__] ];


SyntaxInformation[FTerms] = {"ArgumentsPattern" -> {_, _.}};
FTerms[W_, f_: Identity] :=
  Expand@Collect[Expand@D[W, {Fields@W}], Subscript[X, _][__] .., f@*Simplify];


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
    SameQ @@ FTermsConstraint[W, Abs]
  ];


SyntaxInformation[FEquationsTrivialQ] = {"ArgumentsPattern" -> {_, _.}};
FEquationsTrivialQ[diff_, W_?PotentialQ] :=
  FEquationsTrivialQ[W][diff];
FEquationsTrivialQ[W_?PotentialQ] := 
  Module[{grB, vars},
    vars = Fields@W;
    grB = GroebnerBasis[FTerms@W, vars];
    (PossibleZeroQ@Last@PolynomialReduce[#, grB, vars] &)
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
  Module[{texStr, terms, gather, sorted},
    texStr = ToString[
      W /. {
        Subscript[X, k_][i_, j_] :> If[ 
        FreeQ[ W, Subscript[X, 2][i, j] ], 
        Subscript[ X, Row[{i, j}] ],  Subsuperscript[ X, Row[{i, j}], Row[{k}] ] 
      ]},
      TeXForm];
    terms = StringSplit[texStr, c : {"+", "-"} :> c] // 
      Partition[If[First[#] != "-", Prepend[#, "+"], #], 2] &;
    gather = SortBy[StringCount[Last[#], "X"] &] /@ GatherBy[terms, First];
    sorted = (StringJoin[" ", #1, " ", #2] &) @@@ Join @@ Reverse@SortBy[First@*First]@gather;
    "&= " <> StringReplace[
      StringJoin @@ Riffle[sorted, " \\\\ \n & \\qquad", perline + 1], 
      StartOfLine ~~ " + " -> ""]
  ];


End[]


EndPackage[]
