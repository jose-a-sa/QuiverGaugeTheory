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


SimplifyToricEquations::usage = "";


Begin["`Private`"]


SyntaxInformation[ToGeneratorVariableRules] = {"ArgumentsPattern" -> {_}};

ToGeneratorVariableRules[l : {HoldPattern[Times][Subscript[X, _][__] ..] ..}] :=
  GroupBy[l, Count[ Subscript[X, _][__] ] ] //
    KeyValueMap[Thread[ #2 -> $GeneratorVars[[#1 - 1]] /@ Range[Length@#2] ] &] // 
    Flatten;


SyntaxInformation[ReduceGenerators] = {"ArgumentsPattern" -> {_, _, _.}};

ReduceGenerators[W_ ?PotentialQ, 
    gios : {HoldPattern[Times][Subscript[X, _][__] ..] ..}
  ] := ReduceGenerators[W, gios, Automatic];
ReduceGenerators[W_ ?PotentialQ, 
    gios : {HoldPattern[Times][Subscript[X, _][__] ..] ..}, 
    Automatic
  ] := ReduceGenerators[W, gios, ToGeneratorVariableRules@gios];
ReduceGenerators[W_ ?PotentialQ, 
    gios : {HoldPattern[Times][Subscript[X, _][__] ..] ..}, 
    genRules: ({__Rule} | _Association | Automatic) : Automatic ] :=
  Module[{grB, fields, sol, genDecomp, remDenom},
    fields = Fields@W;
    grB = GroebnerBasis[FTerms@W, fields];
    genDecomp = Reverse@NestWhileList[
      Map[(FirstCase[First@#, _?(Not@*PossibleZeroQ), 1] &)
        ]@PolynomialReduce[#, Keys@genRules, fields] &,   
      Last /@ PolynomialReduce[gios, grB, fields], 
      (Not@*MatchQ[{1 .. }])
    ] // Map[Ratios]@*Transpose // ReplaceAll[genRules] // 
      ApplyTo[Times, {1}];
    remDenom = First@Solve@Cases[
      Thread[Values@KeyTake[gios]@genRules == (Together/@genDecomp)], 
      HoldPattern[Equal][x_,y_] /; UnsameQ[Denominator@y,1]
    ];
    sol = Values@KeyTake[gios]@genRules -> (genDecomp/.remDenom) //
      Thread // Expand // DeleteCases[ HoldPattern[Rule][x_,x_] ];
    Thread[gios -> Expand@(genDecomp/.Echo[sol])]
  ]


SyntaxInformation[SimplifyToricEquations] = {"ArgumentsPattern" -> {_}};

SimplifyToricEquations[expr : (_List | _And)] := 
  Module[{selF, monPatt, l, res},
    l = (If[Equal === Head[#1], #1, Simplify[#1 == 0] ] &) /@ 
      (List @@ expr);
    selF = If[
      SameQ[#2, True] || (LeafCount[#2] > LeafCount[#1]),
      #1, #2 ] &;
    monPatt = Alternatives[
      HoldPattern[Equal][(_Times | _Power), (_Times | _Power)],
      HoldPattern[Equal][ OrderlessPatternSequence[ 0,
        HoldPattern[Plus][(_Times | _Power), (_Times | _Power)] ] ]
    ];
    FixedPoint[
      MapThread[selF, {#, Simplify[#, Select[MatchQ@monPatt]@#]}] &, 
      Expand@l
    ]
 ];


End[]

EndPackage[]
