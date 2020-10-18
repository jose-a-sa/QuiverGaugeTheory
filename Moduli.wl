(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Moduli`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`"
}]


ToGeneratorVariableRules::usage = "";
GeneratorLinearRelations::usage = "";
ReduceGenerators::usage = "";
SingularLocus::usage = "";
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


SyntaxInformation[GeneratorLinearRelations] = {"ArgumentsPattern" -> {_, _}};
GeneratorLinearRelations[W_?PotentialQ, genRules : ({__Rule} | _Association)] :=
  Module[{rel},
    rel = ReplaceAll[genRules]@Expand@Outer[Times, FTerms@W, Fields@W, 1];
    Select[ Flatten@rel, FreeQ[ Subscript[X, _][__] ] ]
  ];


SyntaxInformation[ReduceGenerators] = {
  "ArgumentsPattern" -> {_, _, _, OptionsPattern[]},
  "OptionsName" -> {"RemoveDenominators", "GroebnerBasisMethod"}
};
Options[ReduceGenerators] = {
  "RemoveDenominators" -> False,
  "GroebnerBasisMethod" -> Automatic
}
ReduceGenerators[
    Wgb : (_?PotentialQ | { Except[_List].. }), 
    ops : { Except[_List].. } | Except[_List], 
    Automatic,
    opts : OptionsPattern[] ] :=
  ReduceGenerators[Wgb, ops, ToGeneratorVariableRules@Flatten@{ops}, opts];
ReduceGenerators[
    Wgb : (_?PotentialQ | { Except[_List].. }), 
    ops : Except[_List], 
    genRules : ({__Rule} | _Association),
    opts : OptionsPattern[] ] :=
  First@ReduceGenerators[Wgb, {ops}, genRules, opts];
ReduceGenerators[
    W : _?PotentialQ, 
    ops : { Except[_List].. }, 
    genRules : ({__Rule} | _Association),
    opts : OptionsPattern[] ] :=
  ReduceGenerators[ GroebnerBasis[ FTerms@W, Fields@W, 
      Method -> OptionValue["GroebnerBasisMethod"] ], 
    ops, genRules, opts];
ReduceGenerators[
    gb : { Except[_List].. }, 
    ops : { Except[_List].. }, 
    genRules : ({__Rule} | _Association),
    opts : OptionsPattern[] ] :=
  Module[{dotPR, gens, fields, genDecomp, res, matching, remDenom, sol},
    dotPR[x : {{{__}, _} ..}, l0_List] := Map[dotPR[#, l0] &, x];
    dotPR[{l : {__}, n_?(Not@*MatchQ[_List])}, l0_List] := l0.l + n;
    gens = Association[genRules];
    fields = Fields@gb;
    genDecomp = NestWhile[
      dotPR[PolynomialReduce[#, Keys@gens, fields], Values@gens] &,
      Map[Last]@PolynomialReduce[ops, gb, fields],
      Not@*FreeQ[ Subscript[X,_][__] ]
    ];
    res = Association@Thread[ops -> Expand@genDecomp];
    If[ OptionValue["RemoveDenominators"],
      matching = KeySelect[ res, MatchQ[Alternatives@@Keys@gens] ];
      sol = If[Length[matching] > 0,
        remDenom = First@Solve@Cases[
          KeyValueMap[gens[#1] == Together[#2] &, matching],
          HoldPattern[Equal][x_, y_] /; UnsameQ[Denominator@y, 1]
        ];
        KeyValueMap[gens[#1] -> Together[#2 /. remDenom] &, matching] // 
          DeleteCases[ HoldPattern[Rule][x_, x_] ] // Echo,
        {}
      ];
      KeyValueMap[#1 -> Expand[ #2/.sol ] &, res],
      KeyValueMap[Rule]@res
    ]
  ]


SyntaxInformation[SingularLocus] = {"ArgumentsPattern" -> {_, _}};
SingularLocus[expr : (List|And)[Except[_List]..], v_] :=
  Module[{vars, ideal, jac},
    vars = Flatten[{v}];
    ideal = ToSubtractList[expr];
    jac = D[ideal, {vars}];
    Join[
      DeleteCases[0]@Flatten@Minors[jac, Min@Dimensions@jac], 
      ideal
    ]
  ];


SyntaxInformation[SimplifyToricEquations] = {"ArgumentsPattern" -> {_}};
SimplifyToricEquations[expr : (List|And)[Except[_List]..] ] := 
  Module[{selF, monPatt, l},
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
