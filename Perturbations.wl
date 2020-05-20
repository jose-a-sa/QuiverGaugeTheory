(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Perturbations`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Main`", 
  "QuiverGaugeTheory`Quiver`"
}]


Unprotect["QuiverGaugeTheory`Perturbations`*"];
ClearAll["QuiverGaugeTheory`Perturbations`*"];


FieldRedefinition::usage = "";


RedefinitionMinMonomialCount::usage = "";


MassShiftRules::usage = "";


(* LikelyRedefinitionFields::usage = ""; *)


GeneratorsTable::usage = "";


Begin["`Private`"]


RedefSymbols = {\[Alpha], \[Beta], \[Gamma], \[Delta], \[Epsilon], \[Zeta], \[Eta],
  \[Theta], \[Iota], \[Kappa], \[Lambda], \[Mu], \[Nu], \[Xi],
  \[Omicron], \[Rho], \[Sigma], \[Tau], \[Upsilon], \[Phi], \[Chi],
  \[Psi], \[Omega]};


Options[FieldRedefinition] = {ExcludePureRescalings -> True};
SyntaxInformation[FieldRedefinition] = {
  "ArgumentsPattern" -> {_, _, _, OptionsPattern[]},
  "OptionNames" -> {"ExcludePureRescalings"}
};

FieldRedefinition[fields: { Subscript[X, _][__] .. }, edges_?GraphEdgeQ, deg_, opts:OptionsPattern[] ] := 
  (FieldRedefinition[#, edges, deg, opts] & /@ fields);
FieldRedefinition[Subscript[X, f_][i_, j_], edges_?GraphEdgeQ, deg_, OptionsPattern[] ] :=
  Module[{path, fieldList, redef},
    fieldList = FindQuiverPaths[edges, i, j, deg] // QuiverPathToFields[edges] // 
      Flatten // DeleteCases[ Subscript[X, f][i, j] ];
    redef = Subscript[X, f][i, j] -> Subscript[First@RedefSymbols, f][i, j] Subscript[X, f][i, j] 
      + fieldList.Table[Subscript[RedefSymbols[[k]], f][i, j], {k, 2, Length@fieldList + 1}];
    If[And[OptionValue["ExcludePureRescalings"], fieldList == {}], Nothing, redef]
  ]


SyntaxInformation[RedefinitionMinMonomialCount] = {"ArgumentsPattern" -> {_, _.}};

RedefinitionMinMonomialCount[form_] :=
  RedefinitionMinMonomialCount[#, form] &;
RedefinitionMinMonomialCount[W_, form_] :=
  Total@Coefficient[#,
    Cases[#, 
      Abs@HoldPattern[Times][form, Subscript[\[Alpha], _][__] ..] | 
      Abs@HoldPattern[Times][Subscript[\[Alpha], _][__] ..] |
      Abs[ Subscript[\[Alpha], _][__] ] 
    ] 
  ] & /@ ReplaceAll[HoldPattern[Times][___, _Plus, ___] -> 0]@FTermsConstraint[W, Abs];


SyntaxInformation[LikelyRedefinitionFields] = {"ArgumentsPattern" -> {_, _.}};

LikelyRedefinitionFields[coef_] := 
  LikelyRedefinitionFields[#, coef] &;
LikelyRedefinitionFields[W_?PotentialQ, coef_] := Module[
  {exclude, include},
  exclude = Cases[W //Expand, 
    HoldPattern[Times][1/coef | -(1/coef), a : (Subscript[X, _][__] ..)] :> a
  ] // DeleteDuplicates;
  include = Cases[W // Expand,
    If[exclude == {},
      HoldPattern[Times][-coef | coef, a : (Subscript[X, _][__] ..)] :> a, 
      HoldPattern[Times][-1, a : (Subscript[X, _][__] ..)] | 
      HoldPattern[Times][a : (Subscript[X, _][__] ..)] :> a
    ]
  ] // DeleteDuplicates;
  include // DeleteCases[Alternatives @@ exclude]
];


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


SyntaxInformation[GeneratorsTable] = {"ArgumentsPattern" -> {_, _, _}};

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
  

With[{syms = Names["QuiverGaugeTheory`Perturbations`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[]
 
EndPackage[]
