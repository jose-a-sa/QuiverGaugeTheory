(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["QuiverGaugeTheory`Main`"]
(* Exported symbols added here with SymbolName::usage *)


Unprotect["QuiverGaugeTheory`Main`*"];
ClearAll["QuiverGaugeTheory`Main`*"];


Map[(MessageName[#, "usage"] = "") &,
  ToExpression[{"\[Alpha]", "\[Beta]", "\[Gamma]", "\[Delta]", "\[Epsilon]", "\[Eta]", "\[Lambda]", "\[Xi]", "\[Rho]", "\[Sigma]"},
  InputForm, Hold], {2}]; // ReleaseHold

X::usage = "";
U::usage = "";


FieldsInPotential::usage = "";


FTerms::usage = "";


FTermsConstraint::usage = "";


ChangeGroupIndices::usage = "";


PotentialCoefficientTestQ::usage = "";


PotentialQ::usage = "";


ClosedLoopPotentialQ::usage = "\
\!\(\*RowBox[{\"ClosedLoopPotentialQ\", \"[\", StyleBox[\"W\", \"TI\"], \"]\"}]\) \
yields True if the superpotential \!\(\*StyleBox[\"W\", \"TI\"]\) is the sum of \
closed loop terms. This function does not verify if the superpotential \
\!\(\*StyleBox[\"W\", \"TI\"]\) obeys the F-term equations.";


FEquationsPotentialQ::usage = "\
\!\(\*RowBox[{\"FEquationsPotentialQ\", \"[\", StyleBox[\"W\", \"TI\"], \"]\"}]\) \
yields True if the F-terms for the superpotential \!\(\*StyleBox[\"W\", \"TI\"]\) result in \
exactly 2 monominals with opposite coefficients \[PlusMinus]1.";


Begin["`Private`"] (* Begin Private Context *)


FieldsInPotential[W_] := Cases[
  Expand@W, Subscript[X, _][__], Infinity
] // DeleteDuplicates // Sort;


FTerms[W_, f_: Identity] :=
  Expand@Collect[Expand@D[W, {FieldsInPotential@W}], Subscript[X, _][__] .., f@*Simplify];


FTermsConstraint[W_, f_: Identity] := 
  FTerms[W, f] // ReplaceAll[{Subscript[X, _][__] -> 1}]


PotentialCoefficientTestQ[coefPatt_] := MatchQ[Expand@#, 
  HoldPattern[Plus][(HoldPattern[Times][coefPatt, Subscript[X, _][__] ..] |
   HoldPattern[Times][Subscript[X, _][__] ..]) ..]
] &;


PotentialQ[W_] := PotentialCoefficientTestQ[__][W];


ClosedLoopPotentialQ[W_] := If[!PotentialQ[W], False,
  (Sort[#] == Sort@First@FindCycle[#, Infinity, All] &) /@ 
  Cases[Expand@W, HoldPattern[Times][a___, b:(Subscript[X, _][__] ..)] :>
    ({b} /. {Subscript[X, _] -> DirectedEdge}) /; FreeQ[{a},Subscript[X, _][__]]
  ] // Apply[And]
];


FEquationsPotentialQ[W_] := 
  FullSimplify@And[
    And @@ Thread[FTermsConstraint[W] == 0],
    And @@ Thread[FTermsConstraint[W, Abs] == 2]
  ];


ChangeGroupIndices[list:{__Integer}] := 
  ChangeGroupIndices@Thread[Range@Length[list] -> list];
ChangeGroupIndices[rules : {__Rule} ..] :=
  With[{len = Max@Cases[{rules}, _Integer, Infinity]},
    ChangeGroupIndices[Range[len] -> Fold[ReplaceAll, Range[len], {rules}] // Thread];
  ];
ChangeGroupIndices[i_Integer, j_Integer] := 
  ChangeGroupIndices@Cycles[{{i, j}}];
ChangeGroupIndices[cycles__Cycles] :=
  With[{len = Max@Cases[{cycles}, _Integer, Infinity]},
    ChangeGroupIndices[Range[len] -> Fold[Permute, Range[len], {cycles}] // Thread];
  ]
ChangeGroupIndices[{rules__Rule}] :=
  {Subscript[X, c_][a_, b_] :> Subscript[X, c] @@ ({a, b} /. {rules})};


With[{syms = Names["QuiverGaugeTheory`Main`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[] (* End Private Context *)


EndPackage[]
