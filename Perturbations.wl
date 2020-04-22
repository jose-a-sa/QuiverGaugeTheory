(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Perturbations`", {"QuiverGaugeTheory`Main`", "QuiverGaugeTheory`Quiver`"}]


Unprotect["QuiverGaugeTheory`Perturbations`*"];
ClearAll["QuiverGaugeTheory`Perturbations`*"];


FieldRedefinition::usage = "";


RedefinitionMinMonomialCount::usage = "";


MassShiftRules::usage = "";


(* LikelyRedefinitionFields::usage = ""; *)


FTermsTable::usage = "";


GeneratorsTable::usage = "";


Begin["`Private`"]


RedefSymbols = {\[Alpha], \[Beta], \[Gamma], \[Delta],
  \[Epsilon], \[Eta], \[Lambda], \[Xi], \[Rho], \[Sigma]};


Options[FieldRedefinition] = {ExcludePureRescalings -> True};
SyntaxInformation[FieldRedefinition] = {
  "ArgumentsPattern" -> {_, _, _, OptionsPattern[]},
  "OptionNames" -> {"ExcludePureRescalings"}
};

FieldRedefinition[fields: { Subscript[X, _][__] .. }, edges_?GraphEdgeQ, deg_, opts:OptionsPattern[] ] := 
  (FieldRedefinition[#, edges, deg, opts] & /@ fields);
FieldRedefinition[Subscript[X, f_][i_, j_], edges_?GraphEdgeQ, deg_, OptionsPattern[] ] :=
  Module[{path, fields, redef},
    paths = FindPath[edges, i, j, deg, All] // Map[BlockMap[Apply[DirectedEdge], #, 2, 1] &];
    fieldList = paths // QuiverPathToFields[edges] // DeleteCases[ Subscript[X, f][i, j] ];
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


SyntaxInformation[FTermsTable] = {"ArgumentsPattern" -> {_, _.}};

FTermsTable[W_] := FTermsTable[W, {}]; 
FTermsTable[W_, fList:{(___Function|___Symbol)..}] := 
  Grid[Transpose[{
    FTerms[W, Highlighted],
    Simplify@FTermsConstraint[W], 
    Simplify@FTermsConstraint[W, Abs],
    Sequence@@Table[f@W, {f,fList}]
  }], Frame -> All];


SyntaxInformation[FTermsTable] = {"ArgumentsPattern" -> {_, _, _}};

GeneratorsTable[W_?FEquationsPotentialQ, gen_Association, charges_Association] :=
  Module[{genCol, fieldCol, rCol, trivialCol, fsimp, rsimp},
    fsimp = And@@PossibleZeroQ@FullSimplify[#, 
        Assumptions -> Thread[FTerms[W]==0] 
      ] &;
    rsimp = If[Count[Expand@#, Root[__]^(_.) .., Infinity] > 6, 
        SpanFromLeft, RootReduce[#]
      ] &;  
    genCol = Keys@gen;
    fieldCol = If[Length[{##}] > 1, Equal[##], #] & @@@ Values@gen;
    rCol = List @@@ Keys@gen // 
        ReplaceAll[{x_^y_Integer :> Sequence @@ Table[x, {y}]}] // 
        Map[ Total@*Map[charges] ];
    trivialCol = Values@gen // 
      Map[Rule @@@ TensorTranspose[Subsets[
        Transpose[{Range@Length@#, #}], {2}], {1, 3, 2}] &] // 
      Map@MapAt[fsimp@*First@*Differences, {All, 2}];
    Grid[Transpose[{
      Prepend[genCol, "Generators"], 
      Prepend[fieldCol, "Field generators"],
      Prepend[N@rCol, "R-charge"],
      Prepend[rsimp /@ rCol, SpanFromLeft],
      Prepend[Column /@ trivialCol, "Trivial"]
    } // MapAt[If[StringQ[#], Item[#, ItemSize->{Automatic,1.7}], #] &, {All, 1}]
    ], Frame -> All]
  ];


With[{syms = Names["QuiverGaugeTheory`Perturbations`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[]

EndPackage[]
