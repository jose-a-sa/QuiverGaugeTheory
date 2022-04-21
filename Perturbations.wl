(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Perturbations`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`"
}]


FieldRedefinition::usage = "";
RedefinitionMinMonomialCount::usage = "";
MassShiftRules::usage = "";


$RedefinitionVars = Alternatives@@
  ToExpression@CharacterRange["\[FormalAlpha]", "\[FormalOmega]"];


Begin["`Private`"]



Options[FieldRedefinition] = {
  "ExcludePureRescalings" -> True
};
SyntaxInformation[FieldRedefinition] = {
  "ArgumentsPattern" -> {_, _, _, OptionsPattern[]}
};
FieldRedefinition[fields: {__?FieldQ}, edges: (_?QuiverEdgesQ | _?EdgeListQ ), 
    deg_, opts:OptionsPattern[FieldRedefinition] ] := 
  (FieldRedefinition[#, edges, deg, opts] & /@ fields);
FieldRedefinition[Subscript[X, f_][i_, j_], edges_?QuiverEdgesQ, 
    deg_, opts:OptionsPattern[FieldRedefinition] ] :=
  FieldRedefinition[Subscript[X, f][i, j], Values@edges, deg, opts]
FieldRedefinition[Subscript[X, f_][i_, j_], edges_?EdgeListQ, 
    deg_, OptionsPattern[FieldRedefinition] ] :=
  Module[{fieldList, redef},
    Switch[edges,
      _?(FreeQ[i]), Return@Missing["QuiverVertexAbsent", i],
      _?(FreeQ[j]), Return@Missing["QuiverVertexAbsent", j],
      _, Null];
    fieldList = FindQuiverPaths[edges, i, j, deg] // QuiverPathToFields[edges] // 
      Flatten // DeleteCases[ Subscript[X, f][i, j] ];
    redef = Subscript[X, f][i, j] -> Subscript[First@$RedefinitionVars, f][i, j] Subscript[X, f][i, j] 
      + fieldList.Table[Subscript[$RedefinitionVars[[k+1]], f][i, j], {k, Length@fieldList}];
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
    fields = FieldCases@W;
    vars = fields/.{X -> q};
    rule = Thread[fields -> Power[coef,vars]*fields];
    sol = Last@FindInstance[ And[
      And @@ Thread[Cases[W/.rule // Expand, Times[_., Power[coef, a_] ] :> a] == 0],
      And @@ (restriction /@ vars) ], Evaluate[vars], Integers];
    rule/.sol // DeleteCases[ HoldPattern[Rule][f_, f_] ]
  ];


End[]
 
EndPackage[]
