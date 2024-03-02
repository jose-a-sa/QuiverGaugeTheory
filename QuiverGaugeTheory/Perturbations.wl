(* ::Package:: *)

Unprotect["QuiverGaugeTheory`Perturbations`*"];
ClearAll["QuiverGaugeTheory`Perturbations`*"];


BeginPackage["QuiverGaugeTheory`Perturbations`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`"
}]


FieldRedefinition::usage = "";
RedefinitionMinMonomialCount::usage = "";
MassShiftRules::usage = "";
FindFieldRedefinition::usage = "";


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
    redef = Subscript[X, f][i, j] -> Subscript[First@$RedefinitionVars, f][i, j] Subscript[X, f][i, j] + 
      fieldList.Table[Subscript[$RedefinitionVars[[k+1]], f][i, j], {k, Length@fieldList}];
    If[And[OptionValue["ExcludePureRescalings"], fieldList == {}], Nothing, redef]
  ];
SetAttributes[FieldRedefinition, {Protected, ReadProtected}];


SyntaxInformation[RedefinitionMinMonomialCount] = {"ArgumentsPattern" -> {_, _.}};
RedefinitionMinMonomialCount[form_] :=
  RedefinitionMinMonomialCount[#, form] &;
RedefinitionMinMonomialCount[w_, form_] :=
  Total@Coefficient[#,
    Cases[#, 
      Abs@HoldPattern[Times][form, Subscript[\[FormalAlpha], _][__] ..] | 
      Abs@HoldPattern[Times][Subscript[\[FormalAlpha], _][__] ..] |
      Abs[ Subscript[\[FormalAlpha], _][__] ] 
    ] 
  ] & /@ ReplaceAll[HoldPattern[Times][___, _Plus, ___] -> 0]@FTermsConstraint[w, Abs];
SetAttributes[RedefinitionMinMonomialCount, {Protected, ReadProtected}];


SyntaxInformation[MassShiftRules] = {"ArgumentsPattern" -> {_, _., _.}};
MassShiftRules[coef_, restriction_ : (0<=#<=1 &)] := 
  MassShiftRules[#, coef, restriction] &;
MassShiftRules[w_?PotentialQ, coef_, restriction_ :( 0<=#<=1 &)] := 
  Module[{vars, q, rule, sol, fields},
    fields = FieldCases@w;
    vars = fields/.{X -> q};
    rule = Thread[fields -> Power[coef,vars]*fields];
    sol = Last@FindInstance[ And[
      And @@ Thread[Cases[w/.rule // Expand, Times[_., Power[coef, a_] ] :> a] == 0],
      And @@ (restriction /@ vars) ], Evaluate[vars], Integers];
    rule/.sol // DeleteCases[ HoldPattern[Rule][f_, f_] ]
  ];
SetAttributes[MassShiftRules, {Protected, ReadProtected}];


FindFieldRedefinition[w_?PotentialQ, param_ : Automatic] :=
  Module[{f, aa, vv, possParam, m, redefR0, s, nestF, redefR, ftermsSgn, sgnVars, sgnSol},
    f = FieldCases[w];
    {aa, vv} = {First[$RedefinitionVars], Rest[$RedefinitionVars]};
    possParam = DeleteCases[Variables@Abelianize@w, Alternatives @@ f];
    m = Switch[{param, possParam},
      {Automatic, l_ /; Length[l] == 1}, First[possParam],
      {Except[Automatic, (_Symbol)[__] | _Symbol], _}, param,
      {_, l_ /; Length[l] == 1}, First[possParam],
      _, Message[FindFieldRedefinition::paramerr]; Return[$Failed]
    ];
    If[ToricPotentialQ@Expand@Simplify[m w], 
      Return[{}]
    ];
    redefR0 = FieldRedefinition[FieldCases[w], QuiverFromFields[w], 2];
    If[ Length@redefR0 == 0,
      Message[FindFieldRedefinition::rdfnotavail];
      Return[$Failed];
    ];
    If[Not@AllTrue[ FTermsConstraint[(w/.redefR0), Expand@*Abs, List], 
        Length[#] - Count[#, Abs[_Plus?(Not@*FreeQ[aa|vv]) | _Times?(Not@*FreeQ[vv])], 1] <= 2 & ],
      Message[FindFieldRedefinition::rdfnotposs];
      Return[$Failed];
    ];
    nestF[rule_] := Block[{fterms, active, inactive, h, newR},
      h = Abs@*HoldPattern[Times];
      fterms = FTermsConstraint[m (w /. rule), Abs@*Factor, List];
      active = Union@Join[
        Cases[fterms, h[m^2, Subscript[aa, k1_][i1_, j1_], Subscript[aa, k2_][i2_, j2_] ] :> 
          Splice[{{i1, j1, k1}, {i2, j2, k2}}], 2],
        Cases[fterms, h[m, Subscript[aa, k1_][i1_, j1_]] :> {i1, j1, k1}, 2],
        Cases[fterms, {h[m, Subscript[aa, k1_][i1_, j1_], ___] ..} :> {i1, j1, k1}, 1]
      ];
      inactive = Union @@ Cases[
        Cases[fterms, h[m, Subscript[aa, k1_][i1_, j1_], Subscript[aa, k2_][i2_, j2_]] :> 
          {{i1, j1, k1}, {i2, j2, k2}}, 2],
        {x___, Alternatives @@ active, y___} :> {x, y}
      ];
      newR = Join[
        Apply[ Splice[{Subscript[aa, #3][#1, #2] -> 1, Subscript[vv, #3][#1, #2] -> 0}] &, inactive, {1}],
        Apply[ Splice[{Subscript[aa, #3][#1, #2] -> s[#1, #2, #3]/m,
          (Last@# -> -Total@Most[#] &)@Union@Cases[redefR0, Subscript[aa | vv, #3][#1, #2], Infinity]}] &,
          active, {1}
        ]
      ];
      MapAt[ReplaceRepeated[newR], rule, {All, 2}]
    ];
    redefR = NestWhile[nestF, redefR0, UnsameQ, 2];
    ftermsSgn = FTermsConstraint[m w /. redefR, Simplify@*Abs, List];
    sgnVars = Union@Cases[ftermsSgn, _s, Infinity];
    sgnSol = Select[ 
      AssociationMap[
        Map[Total, (ftermsSgn /. #)] &,
        Thread[sgnVars -> #] & /@ Tuples[{1, -1}, Length@sgnVars]
      ],
      Not@*AnyTrue[True === Simplify[# > 2] &]
    ];
    sgnSol = DeleteCases[{}]@Join[
      Keys@Select[sgnSol, FreeQ[_Abs]],
      KeyValueMap[Join @@ Map[Append[Splice@#1], #2] &]@Map[
        ExpandAll@Normal@Solve[2 == #, Reals, 
          Assumptions -> {m > 0}] &,
        Select[sgnSol, Not@*FreeQ[_Abs]]
      ]
    ];
    redefR = DeleteCases[
      Map[MapAt[ReplaceRepeated[#], redefR, {All, 2}] &, sgnSol],
      {___, HoldPattern[Rule][x_, -x_], ___}
    ];
    redefR = DeleteCases[HoldPattern[Rule][x_, x_]] /@ Select[
      DeleteCases[redefR, {___, HoldPattern[Rule][x_, -x_], ___}],
      Not@PossibleZeroQ@Det@ReplaceAll[Untrace -> 1]@
        DG[Map[Last, #], {Map[First, #]}] &
    ];
    Collect[redefR, _?FieldProductQ | _?FieldQ, Expand]
  ];
FindFieldRedefinition::paramerr = "Parameter not provided and/or ambiguous number of variables in the potential.";
FindFieldRedefinition::rdfnotavail = "There are no field redefinitions available for the quiver associated with this potential.";
FindFieldRedefinition::rdfnotposs = "Field redefinition for this potential does not exist.";
SetAttributes[FindFieldRedefinition, {Protected, ReadProtected}];


End[]
 
EndPackage[]
