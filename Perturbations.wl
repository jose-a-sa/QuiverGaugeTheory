(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Perturbations`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Main`", 
  "QuiverGaugeTheory`Quiver`"
}]


FieldRedefinition::usage = "";


RedefinitionMinMonomialCount::usage = "";


MassShiftRules::usage = "";


GeneratorsTable::usage = "";


Begin["`Private`"]


formalVars = {
  \[FormalAlpha], \[FormalBeta], \[FormalGamma], \[FormalDelta],
  \[FormalCurlyEpsilon], \[FormalZeta], \[FormalEta], \[FormalTheta],
  \[FormalIota], \[FormalKappa], \[FormalLambda], \[FormalMu],
  \[FormalNu], \[FormalXi], \[FormalOmicron], \[FormalPi],
  \[FormalRho], \[FormalFinalSigma], \[FormalSigma], \[FormalTau],
  \[FormalUpsilon], \[FormalCurlyPhi], \[FormalChi], \[FormalPsi],
  \[FormalOmega], \[FormalCurlyTheta], \[FormalPhi], \[FormalCurlyPi],
  \[FormalStigma], \[FormalDigamma], \[FormalKoppa], \[FormalSampi],
  \[FormalCurlyKappa], \[FormalCurlyRho], \[FormalEpsilon]
};


Options[FieldRedefinition] = {ExcludePureRescalings -> True};
SyntaxInformation[FieldRedefinition] = {
  "ArgumentsPattern" -> {_, _, _, OptionsPattern[]},
  "OptionNames" -> {"ExcludePureRescalings"}
};

FieldRedefinition[fields: { Subscript[X, _][__] .. }, edges_?EdgeListQ, deg_, opts:OptionsPattern[] ] := 
  (FieldRedefinition[#, edges, deg, opts] & /@ fields);
FieldRedefinition[Subscript[X, f_][i_, j_], edges_?EdgeListQ, deg_, OptionsPattern[] ] :=
  Module[{path, fieldList, redef},
    Switch[edges,
      _?(FreeQ[i]), Return@Missing["QuiverVertexAbsent", i],
      _?(FreeQ[j]), Return@Missing["QuiverVertexAbsent", j],
      _, Null];
    fieldList = FindQuiverPaths[edges, i, j, deg] // QuiverPathToFields[edges] // 
      Flatten // DeleteCases[ Subscript[X, f][i, j] ];
    redef = Subscript[X, f][i, j] -> Subscript[First@formalVars, f][i, j] Subscript[X, f][i, j] 
      + fieldList.Table[Subscript[formalVars[[k+1]], f][i, j], {k, Length@fieldList}];
    If[And[OptionValue["ExcludePureRescalings"], fieldList == {}], Nothing, redef]
  ]


SyntaxInformation[RedefinitionMinMonomialCount] = {"ArgumentsPattern" -> {_, _.}};

RedefinitionMinMonomialCount[form_] :=
  RedefinitionMinMonomialCount[#, form] &;
RedefinitionMinMonomialCount[W_, form_] :=
  Total@Coefficient[#,
    Cases[#, 
      Abs@HoldPattern[Times][form, Subscript[\[FormalAlpha], _][__] ..] | 
      Abs@HoldPattern[Times][Subscript[\[FormalAlpha], _][__] ..] |
      Abs[ Subscript[\[FormalAlpha], _][__] ] 
    ] 
  ] & /@ ReplaceAll[HoldPattern[Times][___, _Plus, ___] -> 0]@FTermsConstraint[W, Abs];


SyntaxInformation[MassShiftRules] = {"ArgumentsPattern" -> {_, _., _.}};

MassShiftRules[coef_, restriction_ : (0<=#<=1 &)] := 
  MassShiftRules[#, coef, restriction] &;
MassShiftRules[W_?PotentialQ, coef_, restriction_ :( 0<=#<=1 &)] := 
  Module[{vars, q, rule, sol, fields},
    fields = FieldsInPotential@W;
    vars = fields/.{X -> q};
    rule = Thread[fields -> Power[coef,vars]*fields];
    sol = Last@FindInstance[ And[
      And @@ Thread[Cases[W/.rule // Expand, _. Power[coef, a_] :> a] == 0],
      And @@ (restriction /@ vars) ], Evaluate[vars], Integers];
    rule/.sol // DeleteCases[f_ -> f_]
  ];


SyntaxInformation[GeneratorsTable] = {"ArgumentsPattern" -> {_, _., _.}};

GeneratorsTable[W_?ToricPotentialQ, gen_Association, charges_Association] :=
  Module[{genCol, fieldCol, rCol, tdCol, rExactParse},
    rExactParse = If[Count[Expand@#, Root[__]^(_.) .., Infinity] > 10, 
        SpanFromLeft, RootReduce[#] ] &;
    genCol = Keys@gen;
    fieldCol = If[Length[#] > 1, Equal@@#, First@#] & /@ Values[gen];
    rCol = List @@@ Keys[gen] // ReplaceAll[{x_^y_Integer :> Table[x, {y}]}] // 
      Map[Total@*Map[charges]@*Flatten];
    (* FLAG: using SubsetsOld for < 12.0 compatibility *)
    tdCol = Map[Transpose]@*(SubsetsOld[#, {2}] &)@*IndexedList /@ Values[gen] // 
      Map[ If[Length[#] == 0, {Undefined}, 
        ApplyTo[#1 -> FEquationsTrivialQ[Subtract@@#2, W] &, {1}]@#] & ];
    Grid[Transpose[{
      Prepend[genCol, "Generators"], 
      Prepend[fieldCol, "Field generators"],
      Prepend[N /@ rCol, "R-charge"],
      Prepend[rExactParse /@ rCol, SpanFromLeft],
      Prepend[Column /@ tdCol, "Trivial differences"]
    } // MapAt[If[StringQ[#], Item[#, ItemSize->{Automatic,1.7}], #] &, {All, 1}]
    ], Frame -> All]
  ];
  

End[]
 
EndPackage[]
