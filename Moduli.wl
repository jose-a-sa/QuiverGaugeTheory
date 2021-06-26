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
GeneratorsLattice::usage = "";
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
ToGeneratorVariableRules[l : {(_?FieldQ | HoldPattern[Times|CenterDot][__?FieldPowerQ]) ..}] :=
  GroupBy[l, Count[#, _?FieldQ, {0, \[Infinity]}] & ] //
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


Options[ReduceGenerators] = {
  "RemoveDenominators" -> False,
  "GroebnerBasisMethod" -> Automatic
}
SyntaxInformation[ReduceGenerators] = {
  "ArgumentsPattern" -> {_, _, _, OptionsPattern[]}
};
ReduceGenerators[
    Wgb : (_?PotentialQ | { Except[_List].. }), 
    ops : { Except[_List].. } | Except[_List], 
    Automatic,
    opts : OptionsPattern[ReduceGenerators] ] :=
  ReduceGenerators[Wgb, ops, ToGeneratorVariableRules@Flatten@{ops}, opts];
ReduceGenerators[
    Wgb : (_?PotentialQ | { Except[_List].. }), 
    ops : { Except[_List].. } | Except[_List], 
    genRules : (List|Association)[(_ -> _List)..],
    opts : OptionsPattern[ReduceGenerators] ] :=
  ReduceGenerators[Wgb, ops, KeyValueMap[Splice@Thread[#2 -> #1] &]@genRules, opts];
ReduceGenerators[
    Wgb : (_?PotentialQ | { Except[_List].. }), 
    ops : Except[_List], 
    genRules : KeyValuePattern[{}],
    opts : OptionsPattern[ReduceGenerators] ] :=
  First@ReduceGenerators[Wgb, {ops}, genRules, opts];
ReduceGenerators[
    W : _?PotentialQ, 
    ops : { Except[_List].. }, 
    genRules : KeyValuePattern[{}],
    opts : OptionsPattern[ReduceGenerators] ] :=
  ReduceGenerators[ 
    GroebnerBasis[Abelianize@FTerms@W, Fields@W, 
      Method -> OptionValue["GroebnerBasisMethod"] ], 
    ops, genRules, opts];
ReduceGenerators[
    gb : { Except[_List]... }, 
    ops : { Except[_List].. }, 
    genRules : KeyValuePattern[{}],
    opts : OptionsPattern[ReduceGenerators] ] :=
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


SyntaxInformation[GeneratorsLattice] = {"ArgumentsPattern" -> {_, _.}};
GeneratorsLattice[W_?ToricPotentialQ] :=
  Module[{P, pmDecomp, Pmes, Gm, mes, redMes, p, ks},
    mes = GaugeInvariantMesons[QuiverFromFields@W, Infinity];
    P = PerfectMatchingMatrix[W];
    pmDecomp = Map[
      (Times @@ Power[Array[p, Length@#], #] &), 
      AssociationThread[Fields@W, P]
    ];
    ks = GroupBy[mes, ReplaceAll@pmDecomp];
    redMes = Join @@ Values@KeyTake[ks, 
      SortBy[GroebnerBasis@Keys@ks, LeafCount]
    ];
    Pmes = (Exponent[Abelianize@redMes, #] &) /@ Fields[W];
    Gm = NullSpace@NullSpace[Transpose[P].Pmes];
    GroupBy[ Thread[redMes -> If[CoplanarQ@Transpose@Gm, 
        NormalizePolytope@Transpose@Most@Gm, Transpose@Gm]
      ], Last -> First
    ]
  ];


GeneratorsTable::nontoric = "Superpotential or Model provided is not toric."
GeneratorsTable::argw = "Argument provided is not a valid superpotential or Association."
GeneratorsTable::misdata = "Association data provided does not contain all keys: \
\"MesonicGenerators\", \"ChiralMesons\", \"RCharges\", \"GeneratorsLattice\".";
SyntaxInformation[GeneratorsTable] = {"ArgumentsPattern" -> {_}};
GeneratorsTable[W_?ToricPotentialQ] :=
  Module[{td, P, pmDecomp, rchPM, mes, redMes, gen, latt, lattPM},
    td = ToricDiagram[W];
    P = PerfectMatchingMatrix[W];
    latt = GeneratorsLattice[W];
    pmDecomp = Map[
      (Times @@ Power[Keys@td, #] &), 
      AssociationThread[Fields@W, P]
    ];
    rchPM = Last@AMaximization[td];
    mes = GaugeInvariantMesons[QuiverFromFields@W, Infinity];
    redMes = DeleteCases[
      ReduceGenerators[W, Join @@ Values@latt, ToGeneratorVariableRules@mes],
      HoldPattern[Rule][_, _Times | _Power]
    ];
    gen = GroupBy[Keys@redMes, ReplaceAll@pmDecomp];
    lattPM = Map[First]@GroupBy[
      ReplaceAll[pmDecomp]@Normal@latt,
      First@*Last -> First];
    GeneratorsTable@Association[
      "ChiralMesons" -> redMes,
      "MesonicGenerators" -> gen,
      "RCharges" -> rchPM,
      "GeneratorsLattice" -> lattPM
    ]
  ];
GeneratorsTable[data_Association] :=
  Module[{genF, chiralVar, rch, pmColF, fieldColF, chiralColF, sortF,
      latt, rawTable, headings},
    genF = data["MesonicGenerators"];
    chiralVar = Map[ReplaceAll@data["ChiralMesons"], genF];
    rch = AssociationMap[ RootReduce@*ReplaceAll[ 
        KeyMap[Log]@data["RCharges"] 
      ]@*PowerExpand@*Log, Keys[genF]
    ];
    latt = data["GeneratorsLattice"];
    pmColF = ReplaceAll[
      Subscript[x : Except[ \[FormalP] ], i_] :> If[i == 1, x, 1]
    ];
    fieldColF = (If[Length[#] > 1, Tilde @@ #, First@#] &);
    chiralColF = (Column@If[SameQ @@ #, {All -> First[#]},
      KeyValueMap[Reverse@*Rule]@PositionIndex[#]
    ] &);
    sortF = Apply[N@{#2, -Length[First@#4], Mod[ArcTan@@(#3[[{1,2}]] + $MachineEpsilon{-1,1}),2*Pi]} &];
    rawTable = SortBy[sortF]@KeyMap[pmColF]@Merge[
      {genF, rch, latt, chiralVar},
      Apply[{fieldColF@#1, #2, #3, chiralColF@#4} &]
    ];
    headings = {"PM", "Mesonic generators", 
      ToString[Subscript["U"[1], "R"], TraditionalForm], 
      ToString[Superscript["U"[1], 2], TraditionalForm], 
      "Chiral relations"};
    Grid[Join[{headings}, KeyValueMap[{#1,Splice@#2}&]@rawTable],
      ItemSize -> {Automatic, {4, {Automatic}}},
      ItemStyle -> {Automatic, {Bold, {Automatic}}},
      Alignment -> {Center, Center},
      Spacings -> {Automatic, 1}, Frame -> All]
 ] /; AllTrue[{"MesonicGenerators","ChiralMesons","RCharges","GeneratorsLattice"}, (KeyExistsQ[data,#]&)];
GeneratorsTable[W_?PotentialQ] := Message[GeneratorsTable::nontoric];
GeneratorsTable[a_Association] := Message[GeneratorsTable::misdata];
GeneratorsTable[_] := Message[GeneratorsTable::argw];


End[]

EndPackage[]
