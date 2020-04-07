(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["QuiverGaugeTheory`Solvers`", {"QuiverGaugeTheory`Main`"}]
(* Exported symbols added here with SymbolName::usage *)  


Unprotect["QuiverGaugeTheory`Solvers`*"];
ClearAll["QuiverGaugeTheory`Solvers`*"];


Begin["`Private`"] (* Begin Private Context *) 


Vars = Thread[\[Zeta]@Range@Length@#1] &;


VarDictionary[edges_?GraphEdgeQ, deg_] :=
  QuiverLoops[edges, deg] -> Vars@QuiverLoops[edges, deg] //
  Thread // Association;


IntegerVarConstraint[edges_?GraphEdgeQ, deg_] := And[
  And @@ Thread[-1 <= Vars@QuiverLoops[edges, deg] <= 1],
  Element[Alternatives @@ Vars@QuiverLoops[edges, deg], Integers];
]

NonTrivialVarConstraint[edges_?GraphEdgeQ, deg_] :=
  !Vars@QuiverLoops[edges, deg] == Table[0, {Length@QuiverLoops[edges, deg]}];


FTermsVarConstraint[edges_?GraphEdgeQ, deg_, f_: Identity] := FieldsInQuiver[edges] //
  Map[Total@Cases[QuiverLoops[edges, deg].Vars@QuiverLoops[edges, deg], a_ \[Zeta] #1 b__ :> f@a] &]


SumVarConstraint[edges_?GraphEdgeQ, deg_, f_: Identity] := 
  f /@ Vars@QuiverLoops[edges, deg] // Total;


VarsConstraints[edges_?GraphEdgeQ, deg_] := And[
  And @@ Thread[FTermsConstraint[edges, deg] == 0],
  IntegerConstraint[edges, deg],
  NonTrivialConstraint[edges, deg]
];


With[{syms = Names["QuiverGaugeTheory`Solvers`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
]

End[] (* End Private Context *)

EndPackage[]
