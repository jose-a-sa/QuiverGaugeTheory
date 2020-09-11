(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`MesonicBranch`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Main`", 
  "QuiverGaugeTheory`Quiver`"
}]


$GeneratorVars = Alternatives@@
  ToExpression@CharacterRange["\[FormalCapitalA]", "\[FormalCapitalV]"]


ToGeneratorVariableRules::usage = "";


ReduceGenerators::usage = "";


Begin["`Private`"]


SyntaxInformation[ToGeneratorVariableRules] = {"ArgumentsPattern" -> {_}};

ToGeneratorVariableRules[l : {HoldPattern[Times][Subscript[X, _][__] ..] ..}] :=
  GroupBy[l, Count[ Subscript[X, _][__] ] ] //
    KeyValueMap[Thread[ #2 -> $GeneratorVars[[#1 - 1]] /@ Range[Length@#2] ] &] // 
    Flatten;


SyntaxInformation[ReduceGenerators] = {"ArgumentsPattern" -> {_, _, _.}};

ReduceGenerators[W_ ?PotentialQ, 
    gios : {HoldPattern[Times][Subscript[X, _][__] ..] ..}, 
    Automatic ] :=
  ReduceGenerators[W, gios, ToGeneratorVariableRules@gios];
ReduceGenerators[W_ ?PotentialQ, 
    gios : {HoldPattern[Times][Subscript[X, _][__] ..] ..}, 
    genRules: ({__Rule} | _Association | Automatic) : Automatic ] :=
  Module[{grB, fields, result, resultNL, sol, removeDenom},
    fields = Fields@W;
    grB = GroebnerBasis[FTerms@W, fields];
    result = Subtract @@@ Subsets[gios, {2}] // 
      Map[# == Last@PolynomialReduce[#, grB, fields] &] // 
      DeleteCases[True] // ReplaceAll[genRules]@*Expand // 
      Simplify // GroupBy[ FreeQ[ Subscript[X, _][__] ] ];
    resultNL = ( Eliminate[# && And@@Equal@@@
      Select[genRules, ContainsOnly[Fields@#]@*Fields], Fields@#] &) /@ 
      If[KeyExistsQ[result, False], result[False], {}];
    sol = Solve[result[True]~Join~resultNL] //
      DeleteCases[{___, HoldPattern[Rule][_, 0], ___}] // Last;
    removeDenom = Map[First]@GroupBy[Last -> First]@Cases[ sol, 
      HoldPattern[Rule][_, y_] /; 
        (Not@FreeQ[Denominator[y], Alternatives@@$GeneratorVars]) ];
    DeleteCases[sol /. removeDenom, HoldPattern[Rule][x_, x_] ]
  ];


End[]

EndPackage[]
