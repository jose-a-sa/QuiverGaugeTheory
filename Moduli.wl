(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Moduli`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`"
}]


ToGeneratorVariableRules::usage = "";
ReduceGenerators::usage = "";
SimplifyToricEquations::usage = "";
GeneratorsTable::usage = "";


$GeneratorVars = Alternatives@@
  ToExpression@CharacterRange["\[FormalCapitalA]", "\[FormalCapitalT]"];


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


SyntaxInformation[GeneratorsTable] = {"ArgumentsPattern" -> {_, _., _.}};
GeneratorsTable[W_?ToricPotentialQ, gen_Association, charges_Association] :=
  Module[{genCol, fieldCol, rChargeCol, fTermCol, rExactParse, fTermColNumb, feqTrivialQ},
    rExactParse = If[Count[Expand@#, Root[__]^(_.) .., Infinity] > 10, 
        SpanFromLeft, RootReduce[#] ] &;
    feqTrivialQ = FEquationsTrivialQ[W];
    genCol = Keys[gen];
    fieldCol = If[Length[#] > 1, TildeEqual@@#, First@#] & /@ Values[gen];
    rChargeCol = Keys[gen] // Map@RightComposition[
      Apply[List], ReplaceAll[{x_^y_Integer :> Table[x, {y}]}],
      Flatten, ReplaceAll[charges], Total
    ];
    fTermCol = Values[gen] // Map@RightComposition[
      Subsets[#, {2}] &,
      Thread[# -> ApplyTo[feqTrivialQ@*Subtract, {1}]@#] &,
      GroupBy[Last -> Apply[UndirectedEdge]@*First],
      Lookup[#, True, {Undefined}, 
        ApplyTo[Tilde, {1}]@*ConnectedComponents@*Graph] &
    ];
    fTermColNumb =
      MapThread[#1/.Thread[#2->Range@Length@#2] &, {fTermCol, Values@gen}];
    Grid[Transpose[{
      Prepend[genCol, "Generators"], 
      Prepend[fieldCol, "Field generators"],
      Prepend[N /@ rChargeCol, "R-charge"],
      Prepend[rExactParse /@ rChargeCol, SpanFromLeft],
      Prepend[Column@*Sort /@ fTermColNumb, "F-term equiv. GIOs"]
    } // MapAt[If[StringQ[#], Item[#, ItemSize->{Automatic,1.7}], #] &, {All, 1}]
    ], Frame -> All]
  ];


End[]

EndPackage[]
