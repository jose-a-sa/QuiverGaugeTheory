(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Moduli`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Tiling`",
  "QuiverGaugeTheory`Polytope`"
}]


GeneratorRulesQ::usage = "";
ToGeneratorVariableRules::usage = "";
GeneratorLinearRelations::usage = "";
ReduceGenerators::usage = "";
SingularLocus::usage = "";
SimplifyToricEquations::usage = "";
MesonicGenerators::usage = "";
GeneratorsLattice::usage = "";
GeneratorsTable::usage = "";
SubQuiverRepresentations::usage = "";
KahlerChambers::usage = "";
KahlerChambersCompatibility::usage = "";
KahlerChambersFlowGraph::usage = "";
MinimalGLSM::usage = "";
KahlerVolumes::usage = "";


$GeneratorVars::usage = "";


Begin["`Private`"]



$GeneratorVars = Alternatives@@
  ToExpression@Join[
    {"\[FormalCapitalPhi]"},
    CharacterRange["\[FormalCapitalA]", "\[FormalCapitalT]"]
  ];



SyntaxInformation[GeneratorRulesQ] = {"ArgumentsPattern" -> {_}};
GeneratorRulesQ[<|(HoldPattern[Times|CenterDot][__?FieldPowerQ] -> _)..|>] := True;
GeneratorRulesQ[{(HoldPattern[Times|CenterDot][__?FieldPowerQ] -> _)..}] := True;
GeneratorRulesQ[_] := False;



SyntaxInformation[ToGeneratorVariableRules] = {"ArgumentsPattern" -> {_}};
ToGeneratorVariableRules[l : {(_?FieldQ | HoldPattern[Times|CenterDot][__?FieldPowerQ]) ..}] :=
  GroupBy[l, Count[#, _?FieldQ, {0, \[Infinity]}] & ] //
    KeyValueMap[Thread[ #2 -> $GeneratorVars[[#1]] /@ Range[Length@#2] ] &] // 
    Flatten;



SyntaxInformation[GeneratorLinearRelations] = {"ArgumentsPattern" -> {_, _}};
GeneratorLinearRelations[W_?AbelianPotentialQ, genRules : KeyValuePattern[{}] ] :=
  Module[{rel, gens},
    gens = If[AssociationQ@genRules, 
      KeyValueMap[Abelianize@#1 -> #2 &, genRules],
      MapAt[Abelianize, genRules, {All, 1}]
    ];
    rel = ReplaceAll[gens]@Expand@Outer[Times, FTerms@W, FieldCases@W, 1];
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
    GroebnerBasis[Abelianize@FTerms@W, FieldCases@W, 
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
    fields = FieldCases@gb;
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



SyntaxInformation[MesonicGenerators] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};
MesonicGenerators[W_?ToricPotentialQ, OptionsPattern[{Method -> Automatic}] ] :=
  Module[{P, pms, pmDecomp, Pmes, Gm, mes, redMes, ks},
    mes = GaugeInvariantMesons[QuiverFromFields@W, Infinity];
    P = PerfectMatchingMatrix[W];
    pms = Switch[OptionValue[Method],
      "Fast" | "Faster", 
      Array[Subscript[\[FormalCapitalP], #] &, Last@Dimensions@P],
      Automatic | "ToricDiagram", 
      Keys@ToricDiagram[W],
      _, Keys@ToricDiagram[W]
    ];
    pmDecomp = Map[(Times @@ Power[pms, #] &),
      AssociationThread[FieldCases@W, P]
    ];
    ks = GroupBy[mes, ReplaceAll@pmDecomp];
    KeyTake[ks, SortBy[GroebnerBasis@Keys@ks, LeafCount] ]
  ];



SyntaxInformation[GeneratorsLattice] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};
GeneratorsLattice[W_?ToricPotentialQ] :=
  Module[{P, Pmes, Gm, redMes, ch},
    P = PerfectMatchingMatrix[W];
    redMes = Join @@ Values@MesonicGenerators[W, Method -> "Fast"];
    Pmes = (Exponent[Abelianize@redMes, #] &) /@ FieldCases[W];
    Gm = NullSpace@NullSpace[Transpose[P].Pmes];
    ch = If[CoplanarQ@Transpose@Gm, 
      NormalizePolytope@Transpose@Most@Gm, 
      Transpose@Gm];
    GroupBy[Thread[redMes -> ch], Last -> First]
  ];



SyntaxInformation[GeneratorsTable] = {"ArgumentsPattern" -> {_}};
GeneratorsTable[W_?ToricPotentialQ] :=
  Module[{td, P, pmDecomp, rchPM, mes, redMes, gen, latt, lattPM},
    td = ToricDiagram[W];
    P = PerfectMatchingMatrix[W];
    latt = GeneratorsLattice[W];
    pmDecomp = Map[
      (Times @@ Power[Keys@td, #] &), 
      AssociationThread[FieldCases@W, P]
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
GeneratorsTable::nontoric = "Superpotential or Model provided is not toric."
GeneratorsTable::argw = "Argument provided is not a valid superpotential or Association."
GeneratorsTable::misdata = "Association data provided does not contain all keys: \
\"MesonicGenerators\", \"ChiralMesons\", \"RCharges\", \"GeneratorsLattice\".";



SyntaxInformation[SubQuiverRepresentations] = {"ArgumentsPattern" -> {_,_.}};
SubQuiverRepresentations[W_?ToricPotentialQ] := 
  SubQuiverRepresentations[W, Automatic];
SubQuiverRepresentations[W_?ToricPotentialQ, pmPairs : {__} | Automatic] :=
  Module[{td, P, pm, Q, properRep, F, allReps, pairs},
    Q = QuiverFromFields@W;
    td = ToricDiagram[W];
    F = Sort@VertexList[Values@Q];
    P = PerfectMatchingMatrix[W];
    pm = AssociationThread[Keys@td, DeleteCases[Keys[Q]^#, 1] & /@ Transpose@P];
    allReps = Subsets[F, {1, Length[F] - 1}];
    properRep = g |-> Select[allReps, 
      ContainsExactly[VertexOutComponent[g, #], #] &];
    pairs = If[MatchQ[pmPairs, Automatic], List /@ Keys@td, List @@@ pmPairs];
    AssociationMap[
      properRep@Values@KeyDrop[ Q, Flatten[# /. pm] ] &, 
      pairs
    ]
  ];



SimplifyThetaCondition[k_Integer] :=
  SimplifyThetaCondition[Range@k];
SimplifyThetaCondition[F_List] :=
  Module[{Fivars, rule},
    Fivars = Map[$FayetIliopoulosVar, Sort@F];
    rule = Last[Fivars] -> -Total@Most[Fivars];
    ReplaceAll[rule]
  ];
ToNonStrict = ReplaceAll[{Greater -> GreaterEqual, Less -> LessEqual}];
ToStrict = ReplaceAll[{GreaterEqual -> Greater, LessEqual -> Less}];



SyntaxInformation[KahlerChambers] = {"ArgumentsPattern" -> {_}};
KahlerChambers[W_?ToricPotentialQ] :=
  KahlerChambers[ToricDiagram@W];
KahlerChambers[td: KeyValuePattern[{}]?ToricDiagramQ] :=
  Module[{tdG},
    tdG = SortBy[{Length@#, #} &]@PositionIndex[td];
    AssociationThread[Keys@tdG, #] & /@ Tuples[Values@tdG]
  ];



Options[KahlerChambersCompatibility] := DeleteDuplicatesBy[First]@{
  "ShowProgress" -> False
};
SyntaxInformation[KahlerChambersCompatibility] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]}
};
KahlerChambersCompatibility[W_?ToricPotentialQ, 
    opts: OptionsPattern[KahlerChambersCompatibility] ] :=
  Module[{k, status, indicator, td, triang, triangEdgesF, lenK,
      KC, F, stabilityC, tbPairs, pairsR, properPairs, tb},
    F = Sort@VertexList[Values@QuiverFromFields@W];
    simpT = SimplifyThetaCondition[F];
    td = ToricDiagram[W];
    triang = PolytopeTriangulations[Values@td];
    triangEdgesF = (Identity @@@ MeshCells[#, 1] /. MapIndexed[
      First@#2 -> #1 &, Rationalize@MeshCoordinates@#] &);
    KC = KahlerChambers[td];
    stabilityC = Apply[And]@*Map[ LessThan[0]@*Total@*Map[$FayetIliopoulosVar] ];
    tbPairs = Outer[Join[(#1 /. #2), 
      List /@ DeleteCases[ Subscript[$ExtremalPerfectMatchingVar,_] ]@Values@#2] &,
      Map[triangEdgesF, triang], KC, 1];
    properPairs = DeleteDuplicatesBy[Sort]@Flatten[tbPairs, 2];
    {k, lenK, status} = {0, Length@properPairs,
      "Simplifying theta-stability from sub-quiver representations..."};
    If[OptionValue["ShowProgress"] === True, 
      PrintTemporary@Labeled[
        ProgressIndicator[Dynamic[k], {0, Dynamic[lenK]}, 
          BaselinePosition->Scaled[0.1] ],
        Style[Dynamic[status], FontFamily -> Automatic], 
        Right
      ]
    ];
    pairsR = Map[
      Block[{},
        k++;
        Simplify@simpT@stabilityC[#]
      ] &, 
      SubQuiverRepresentations[W, properPairs]
    ];
    {k, lenK, status} = {0, Times @@ (Dimensions[tbPairs][[{1,2}]]),
      "Simplifying compatibility table entries..."};
    tb = Map[
      Block[{},
        k++;
        ToNonStrict@FullSimplify@Apply[And, #]
      ] &,
      tbPairs /. Normal@KeyMap[#1 | Reverse@#1 &]@pairsR, 
      {2}
    ];
    status = "Done!";
    AssociationThread[triang, (AssociationThread[KC, #] &) /@ tb]
  ];



kcTablePattQ = MatchQ[
  KeyValuePattern[_MeshRegion -> KeyValuePattern[
    KeyValuePattern[{{__?NumericQ} -> Subscript[$PerfectMatchingVars, _]}] -> _]
  ]
];
Options[KahlerChambersFlowGraph] := DeleteDuplicatesBy[First]@{
  "RegionTests" -> Automatic,
  "ShowProgress" -> False
};
SyntaxInformation[KahlerChambersFlowGraph] = {
  "ArgumentsPattern" -> {_, _, OptionsPattern[]}
};
KahlerChambersFlowGraph[WI_?ToricPotentialQ, WF_?ToricPotentialQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] :=
  KahlerChambersFlowGraph[
    KahlerChambersCompatibility[WI, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    KahlerChambersCompatibility[WF, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    opts];
KahlerChambersFlowGraph[WI_?ToricPotentialQ, tbF_?kcTablePattQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] :=
  KahlerChambersFlowGraph[
    KahlerChambersCompatibility[WI, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    tbF, 
    opts];
KahlerChambersFlowGraph[tbI_?kcTablePattQ, WF_?ToricPotentialQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] :=
  KahlerChambersFlowGraph[
    tbI,
    KahlerChambersCompatibility[WF, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    opts];
KahlerChambersFlowGraph[tbI_?kcTablePattQ, tbF_?kcTablePattQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] := 
  Module[{k = 0, oskcI, oskcF, trigI, trigF, meshToGr, kcRulesFunc,
      kcRulesI, kcRulesF, vars, testRules, graph, indicator, status},
    {trigI, trigF} = Keys /@ {tbI, tbF};
    {oskcI, oskcF} = Keys /@ {First@tbI, First@tbF};
    kcRulesFunc = {tb, oskc, trig} |-> DeleteCases[False]@Association[Join @@ 
      MapThread[Rule, {Outer[List, trig, oskc, 1], Map[Values, tb, {0, 1}]}, 2]
    ];
    {status, indicator} = {"Simplifying theta-stability conditions...",
      ProgressIndicator[Appearance -> "Indeterminate", BaselinePosition -> Scaled[0.1] ]};
    If[OptionValue["ShowProgress"] === True, 
      PrintTemporary@Dynamic[Labeled[Dynamic[indicator],
        Style[Dynamic[status], FontFamily -> Automatic], Right]
      ]
    ];
    {kcRulesI, kcRulesF} = kcRulesFunc @@@ {
      {tbI, oskcI, trigI}, {tbF, oskcF, trigF}};
    vars = Sort@UniqueCases[Values /@ {kcRulesI, kcRulesF}, $FayetIliopoulosVar[_] ];
    testRules = Switch[OptionValue["RegionTests"],
      KeyValuePattern[{}], Normal@OptionValue["RegionTests"],
      _, {
        (RegionWithin[#2, #1] &) -> DirectedEdge,
        (RegionWithin) -> (DirectedEdge[#2, #1] &)
      }
    ];
    {status, indicator} = {"Comparing chambers from both models...",
      ProgressIndicator[Dynamic[k], {0, Length[kcRulesI]*Length[kcRulesF]}, 
        BaselinePosition -> Scaled[0.1] ]};
    graph = Join @@ Outer[
      Block[{}, 
        k++;
        Splice@Apply[
          {f1, f2} |-> If[f1 @@ Map[Last, {##}], f2 @@ Map[First, {##}], Nothing], 
          testRules, {1}]
      ] &,
      Normal[ImplicitRegion[#, Evaluate@vars] & /@ kcRulesI],
      Normal[ImplicitRegion[#, Evaluate@vars] & /@ kcRulesF],
      1
    ];
    status = "Done!";
    Graph[graph]
  ];



Options[MinimalGLSM] := {
  "BasisMethod" -> Automatic
};
SyntaxInformation[MinimalGLSM] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]}
};
MinimalGLSM[W_?ToricPotentialQ, opts : OptionsPattern[MinimalGLSM] ] :=
  Module[{FIvar, simpF, ff, td, F, simpT, pms, KC, vars, thetaC, subQReps, 
      regKC, eqs, eqsKC, linEqs, basis, G},
    FIvar = $FayetIliopoulosVar;
    simpF = FullSimplify[#, Element[FIvar[_], Reals] ] &;
    {ff, td, KC} = {FastForward[W], ToricDiagram[W], KahlerChambers[W]};
    G = Length[ ff["QDb"] ];
    subQReps = KeyMap[First]@SubQuiverRepresentations[W];
    F = Sort@VertexList[Values@QuiverFromFields@W];
    simpT = SimplifyThetaCondition[F];
    pms = Keys[td];
    vars = Sort@KeyValueMap[Subscript[First[#2], #1] &, First@KC];
    thetaC = Apply[ And[##, Total@Array[FIvar, G] == 0] &
      ]@*Map[LessEqualThan[0]@*Total@*Map[FIvar] ];
    regKC = Map[Simplify@*simpT@*thetaC,
      Join @@@ (Map[Values, KC] /. subQReps)];
    eqs = Join[
      If[ff["QF"] == {}, {}, ff["QF"] . pms],
      If[ff["QDb"] == {}, {}, ff["QDb"] . pms - Array[FIvar, G] ]
    ];
    eqsKC = Map[
      ToSubtractList@simpF@simpT@Eliminate[0 == (eqs/.#), pms] &,
      KeyValueMap[#2 -> Subscript[First[#2], #1] &] /@ KC
    ];
    linEqs = {D[#, {vars}], Transpose[{D[#, {vars}] . vars - #}]} & /@ eqsKC;
    basis = List @@ minimalGLSMBasis[
      linEqs, regKC, Last /@ vars,
      OptionValue["BasisMethod"]
    ];
    If[FailureQ@basis, Return@$Failed];
    AssociationThread @@ MapAt[AssociationThread[vars, #] &, basis, {1, All}]
  ];
MinimalGLSM::mtharg = "Option value `1` for \"BasisMethod\" is not valid. \
Use methods \"PositiveVolumes\", \"ToricDiagramKernel\" or \"MatchFirst\".";


minimalGLSMBasis[eqs : {{_?MatrixQ, _?MatrixQ} ..}, reg_List, pt : {{_, _} ..}, m_] :=
  Module[{glZ, reducePwF, simpF, toPiecewise, charges, vols, n,
      ptCharges, minCoefCases, getVols, final},
    reducePwF = Through@*If[MatchQ[_Piecewise], 
      MapAt[Reduce[#, Reals] &, {1, All, 2}], Identity];
    simpF = FullSimplify[#, Element[$FayetIliopoulosVar[_], Reals] ] &;
    {charges, vols} = Transpose[eqs];
    n = Length@First@charges;
    ptCharges = NullSpace@Transpose@Join[pt, Table[{1}, Length@pt], 2];
    glZ := Select[Tuples[Range[-3, 3], {n, n}], Abs@Det[#1] == 1 &];
    minCoefCases := Values@DeleteDuplicatesBy[
      AssociationMap[# . ptCharges &, glZ], Sort];
    toPiecewise = reducePwF@simpF@Piecewise[Transpose@{#, reg}] &;
    getVols[ch_] := Map[toPiecewise]@Transpose[
      SolveMatrixLeft[#1, ch] . Flatten[#2] & @@@ eqs];
    final = Switch[m,
      Automatic | "ToricDiagramKernel",
      AssociationMap[getVols, {ptCharges}],
      "PositiveVolumes",
      Select[AssociationMap[getVols, minCoefCases],
        MatchQ[{True ..}|True]@*Map[(Reduce[# >= 0, Reals] &)]
      ],
      "MatchFirst",
      AssociationMap[getVols, {charges[[1]]}],
      _, Message[MinimalGLSM::mtharg, m]; Return[$Failed]
    ];
    Last@MaximalBy[Normal@final,
      (Join[Count[0] /@ #, Count[_?Positive] /@ #] &)@*First
    ]
  ];



Options[KahlerVolumes] := {
  "ShowProgress" -> False
};
SyntaxInformation[KahlerVolumes] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]}
};
KahlerVolumes[W_?ToricPotentialQ, opts : OptionsPattern[KahlerVolumes] ] :=
  Module[{r, F, td, ff, KC, triang, pms, eqs, triangPairs, 
      cycleVol, cycleVolF, k, status, lenK, res},
    F = Sort@VertexList[Values@QuiverFromFields@W];
    {td, ff} = {ToricDiagram[W], FastForward[W]};
    KC = KahlerChambers[td];
    triang = PolytopeTriangulations[Values@td];
    pms = Keys[td];
    eqs = SimplifyThetaCondition[F]@Join[
      If[ff["QF"] == {}, {}, ff["QF"] . (pms^2)],
      If[ff["QDb"] == {}, {}, ff["QDb"] . (pms^2) - Map[$FayetIliopoulosVar,F] ]
    ];
    triangPairs = AssociationMap[triangulationFacePairs, triang];
    cycleVol = (r /. First@Solve[Eliminate[
        0 == Join[eqs /. Thread[#1 -> 0], {Dot[#2, #2] - r}],
      pms], r] &);
    {k, lenK, status} = {0, Length[KC]*Length[triang],
      "Computing volumes..."};
    If[OptionValue["ShowProgress"] === True, 
      PrintTemporary@Labeled[
        ProgressIndicator[Dynamic[k], {0, Dynamic[lenK]}, 
          BaselinePosition->Scaled[0.1] ],
        Style[Dynamic[status], FontFamily -> Automatic], 
        Right
      ]
    ];
    cycleVolF = {trg, kc} |-> Block[{},
      k++;
      Association@Apply[
        Sort[(#1 /. td)] -> cycleVol[#1, #2] &,
        (trg /. triangPairs /. kc), {1}]
    ];
    res = AssociationThread[triang,
      Association /@ Apply[#2 -> cycleVolF[#1, #2] &, 
        Outer[List, triang, KC, 1], {2}]
    ];
    status = "Done!";
    res
  ];


triangulationFacePairs[trig_?PolytopeTriangulationQ] :=
  Module[{ptsR, faceR, pairs},
    ptsR = ReplaceAll@MapIndexed[
      (Join[{0}, #2] | First[#2]) -> #1 &, 
      Rationalize@MeshCoordinates@#] &;
    faceR = ReplaceAll@MapIndexed[
      (Join[{2}, #2] | First[#2]) -> #1 &, 
      Identity @@@ MeshCells[#, 2]
    ] &; 
    Map[{Intersection @@ #, SymmetricDifference @@ #} &,
      ptsR[trig]@faceR[trig]@EdgeList@MeshConnectivityGraph[trig, 2]
    ]
  ];



End[]

EndPackage[]
