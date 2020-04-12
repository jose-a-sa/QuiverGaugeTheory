(* Wolfram Language Package *)

BeginPackage["QuiverGaugeTheory`Perturbations`", {"QuiverGaugeTheory`Main`", "QuiverGaugeTheory`Quiver`"}]
(* Exported symbols added here with SymbolName::usage *)  


Unprotect["QuiverGaugeTheory`Perturbations`*"];
ClearAll["QuiverGaugeTheory`Perturbations`*"];


FieldRedefinition::usage = "";


RedefMinMonomialCount::usage = "";


FTermsTable::usage = "";


GeneratorsTable::usage = "";


Begin["`Private`"] (* Begin Private Context *)


RedefSymbols = {\[Alpha], \[Beta], \[Gamma], \[Delta],
  \[Epsilon], \[Eta], \[Lambda], \[Xi], \[Rho], \[Sigma]};


FieldRedefinition[fields: { Subscript[X, _][__] .. }, edges_?GraphEdgeQ, deg_, factor_: 1] := 
  (FieldRedefinition[#, edges, deg, factor] & /@ fields);
FieldRedefinition[Subscript[X, f_][i_, j_], edges_?GraphEdgeQ, deg_, factor_: 1] :=
  FindPath[edges, i, j, deg, All] // Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &] // 
    QuiverPathToFields[edges] // DeleteCases[ Subscript[X, f][i, j] ] // 
    Subscript[X, f][i, j] -> Subscript[First@RedefSymbols, f][i, j] Subscript[X, f][i, j] + 
      #1.Table[Subscript[RedefSymbols[[k]], f][i, j], {k, 2, Length@#1 + 1}] &;


RedefMinMonomialCount[form_] := Total@Coefficient[#, Cases[#, 
    Abs@HoldPattern[Times][form, Subscript[\[Alpha], _][__] ..] | 
    Abs@HoldPattern[Times][Subscript[\[Alpha], _][__] ..] |
    Abs[ Subscript[\[Alpha], _][__] ] 
  ]
] &;


FTermsTable[W_] := FTermsTable[W, {}]; 
FTermsTable[W_, fList:{(___Function|___Symbol)..}] := 
  Grid[Transpose[{
    FTerms[W, Highlighted],
    Simplify@FTermsConstraint[W], 
    Simplify@FTermsConstraint[W, Abs],
    Sequence@@Table[f@W, {f,fList}]
  }], Frame -> All];


GeneratorsTable[gen_Association, charges_Association] := 
  Grid[Transpose[{
    Keys@gen,
    If[Length[{##}] > 1, Equal[##], #] & @@@ Values@gen, 
    List @@@ Keys@gen // 
      ReplaceAll[{x_^y_Integer :> Sequence @@ Table[x, {y}]}] // 
      Map[ FullSimplify@*Total@*Map[charges] ],
    List @@@ Keys@gen // 
      ReplaceAll[{x_^y_Integer :> Sequence @@ Table[x, {y}]}] // 
      Map[ N@*Total@*Map[charges] ]
  }], Frame -> All];
  

With[{syms = Names["QuiverGaugeTheory`Perturbations`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[] (* End Private Context *)

EndPackage[]