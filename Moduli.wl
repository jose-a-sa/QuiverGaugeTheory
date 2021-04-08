(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Moduli`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Tiling`",
  "QuiverGaugeTheory`Polytope`"
}]


GeneratorRulesQ::usage = "";
ReplaceTraces::usage = "";
ToGeneratorVariableRules::usage = "";
GeneratorLinearRelations::usage = "";
ReduceGenerators::usage = "";
SingularLocus::usage = "";
SimplifyToricEquations::usage = "";
GeneratorsTable::usage = "";


$GeneratorVars = Alternatives@@
  ToExpression@Join[
    {"\[FormalCapitalPhi]"},
    CharacterRange["\[FormalCapitalA]", "\[FormalCapitalT]"]
  ];


Begin["`Private`"]


SyntaxInformation[GeneratorRulesQ] = {"ArgumentsPattern" -> {_}};
GeneratorRulesQ[<|(HoldPattern[Times|CenterDot][__?FieldPowerQ] -> _)..|>] := True;
GeneratorRulesQ[{(HoldPattern[Times|CenterDot][__?FieldPowerQ] -> _)..}] := True;
GeneratorRulesQ[_] := False;


SyntaxInformation[ReplaceTraces] = {"ArgumentsPattern" -> {_}};
ReplaceTraces[gens_?GeneratorRulesQ][expr_] := 
 ReplaceAll[
   MapAt[Alternatives @@ 
       Table[RotateLeft[#, i], {i, Length[#]}] &, {All, 1}]@
    If[AssociationQ@gens, KeyValueMap[List, gens], gens]][expr]


SyntaxInformation[ToGeneratorVariableRules] = {"ArgumentsPattern" -> {_}};
ToGeneratorVariableRules[l : {HoldPattern[Times|CenterDot][__?FieldPowerQ] ..}] :=
  GroupBy[l, Count[_?FieldQ] ] //
    KeyValueMap[Thread[ #2 -> $GeneratorVars[[#1]] /@ Range[Length@#2] ] &] // 
    Flatten;


SyntaxInformation[GeneratorLinearRelations] = {"ArgumentsPattern" -> {_, _}};
GeneratorLinearRelations[W_?AbelianPotentialQ, genRules : KeyValuePattern[{}]] :=
  Module[{rel, gens},
    gens = If[AssociationQ@genRules, 
      KeyValueMap[Abelianize@#1 -> #2 &, genRules],
      MapAt[Abelianize, genRules, {All, 1}]
    ];
    rel = ReplaceAll[gens]@Expand@Outer[Times, FTerms@W, Fields@W, 1];
    Select[ Flatten@rel, FreeQ[_?FieldQ] ]
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
    ops : { Except[_List].. } | Except[_List], 
    genRules : (List|Association)[(_ -> _List)..],
    opts : OptionsPattern[] ] :=
  ReduceGenerators[Wgb, ops, KeyValueMap[Splice@Thread[#2 -> #1] &]@genRules, opts];
ReduceGenerators[
    Wgb : (_?PotentialQ | { Except[_List].. }), 
    ops : Except[_List], 
    genRules : KeyValuePattern[{}],
    opts : OptionsPattern[] ] :=
  First@ReduceGenerators[Wgb, {ops}, genRules, opts];
ReduceGenerators[
    W : _?PotentialQ, 
    ops : { Except[_List].. }, 
    genRules : KeyValuePattern[{}],
    opts : OptionsPattern[] ] :=
  ReduceGenerators[ 
    GroebnerBasis[Abelianize@FTerms@W, Fields@W, 
      Method -> OptionValue["GroebnerBasisMethod"] ], 
    ops, genRules, opts];
ReduceGenerators[
    gb : { Except[_List].. }, 
    ops : { Except[_List].. }, 
    genRules : KeyValuePattern[{}],
    opts : OptionsPattern[] ] :=
  Module[{dotPR, gens, fields, genDecomp, res, matching, remDenom, sol},
    dotPR[x : {{{__}, _} ..}, l0_List] := Map[dotPR[#, l0] &, x];
    dotPR[{l : {__}, n_?(Not@*MatchQ[_List])}, l0_List] := l0.l + n;
    gens = Association[genRules];
    fields = Fields@gb;
    Message[Abelianize::warn];
    genDecomp = NestWhile[
      dotPR[PolynomialReduce[#, Abelianize@Keys@gens, fields], Values@gens] &,
      Map[Last]@PolynomialReduce[Abelianize@ops, Abelianize@gb, fields],
      Not@*FreeQ[_?FieldQ]
    ];
    res = AssociationThread[ops, Expand@genDecomp];
    If[ OptionValue["RemoveDenominators"],
      matching = KeySelect[res, 
        MatchQ[#, Alternatives@@ Keys@gens] &
      ];
      sol = If[Length[matching] > 0,
        remDenom = First@Solve@Cases[
          KeyValueMap[gens[#1] == Together[#2] &, matching],
          HoldPattern[Equal][x_, y_] /; UnsameQ[Denominator@y, 1]
        ];
        KeyValueMap[gens[#1] -> Together[#2 /. remDenom] &, matching] // 
          DeleteCases[ HoldPattern[Rule][x_, x_] ],
        {}
      ];
      KeyValueMap[#1 -> Expand[#2/.sol] &, res],
      Normal@res
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


GeneratorsTable::nontoric = "Superpotential or Model provided is not toric."
GeneratorsTable::argw = "Argument provided is not a valid superpotential or Association."
GeneratorsTable::misdata = "Association data provided does not contain all keys: \
\"MesonicGenerators\", \"ChiralMesons\" and \"RCharges\".";
SyntaxInformation[GeneratorsTable] = {"ArgumentsPattern" -> {_}};
GeneratorsTable[W_?ToricPotentialQ] :=
  Module[{td, P, pmDecomp, rchPM, mes, redMes, gen},
    td = ToricDiagram[W];
    P = PerfectMatchingMatrix[W];
    pmDecomp = Map[
      (Times @@ Power[Keys@td, #] &),
      AssociationThread[Fields@W, P]
    ];
    rchPM = Last@AMaximization[td];
    mes = GaugeInvariantMesons[QuiverFromFields@W, Infinity];
    redMes = GroupBy[Last -> First]@DeleteCases[
      ReduceGenerators[W, mes, Automatic],
      HoldPattern[Rule][_, _Times|_Power]
    ];
    gen = GroupBy[Join @@ Values@redMes, ReplaceAll@pmDecomp];
    GeneratorsTable@Association[
      "ChiralMesons" -> redMes,
      "MesonicGenerators" -> gen,
      "RCharges" -> rchPM
    ]
  ];
GeneratorsTable[data_Association] :=
  Module[{chiralMes, gen, rch, contractPM, 
      genCol, fieldCol, rChargeCol, chiralCol, headings, sortF},
    gen = data["MesonicGenerators"];
    chiralMes = data["ChiralMesons"];
    rch = data["RCharges"];
    contractPM = ReplaceAll[ 
      Subscript[x : Except[ \[FormalP] ], i_] :> If[i==1,x,1] 
    ];
    tildeF = (If[Length[#]>1, Tilde@@#, First@#] &);
    genCol = contractPM /@ Keys[gen];
    fieldCol = tildeF /@ Values[gen];
    rChargeCol = List @@@ Keys[gen] // 
      ReplaceAll[Power -> Splice@*ConstantArray] //
      ReplaceAll[rch] // Map[ RootReduce@*Total@*Select[NumericQ] ];
    (* chiralCol = Values@*Map[tildeF]@*PositionIndex /@ 
      ReplaceAll[ KeyValueMap[Splice@Thread[#2->#1] &, chiralMes] ]@Values[gen]; *)
    chiralCol = Column@*KeyValueMap[Reverse@*Rule]@*PositionIndex /@
      ReplaceAll[ KeyValueMap[Splice@Thread[#2->#1] &, chiralMes] ]@Values[gen];
    headings = {
      "Perfect Matching", 
      "Mesonic generators", 
      "R-charge", 
      "Chiral Ring relations"
    };
    sortF = Apply[{N[#3],-Length[#4]} &];
    Grid[
      Join[
        {headings},
        SortBy[sortF]@Transpose[
          {genCol, fieldCol, rChargeCol, chiralCol}]
      ],
      ItemSize -> {{10, Automatic, 8, 10}, {4, {Automatic}}},
      ItemStyle -> {Automatic, {Bold, {Automatic}}},
      Alignment -> {Center, Center},
      Spacings -> {Automatic, 1},
      Frame -> All
    ]
  ] /; AllTrue[{"MesonicGenerators","ChiralMesons","RCharges"}, (KeyExistsQ[data,#]&)];
GeneratorsTable[W_?PotentialQ] := Message[GeneratorsTable::nontoric];
GeneratorsTable[a_Association] := Message[GeneratorsTable::misdata];
GeneratorsTable[_] := Message[GeneratorsTable::argw];


End[]

EndPackage[]
