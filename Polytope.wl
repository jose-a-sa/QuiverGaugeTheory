(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Polytope`", {"QuiverGaugeTheory`Main`"}]


Unprotect["QuiverGaugeTheory`Polytope`*"];
ClearAll["QuiverGaugeTheory`Polytope`*"];


DualPolytope::usage = "";


PolytopeVertices::usage = "";


PolytopePlot::usage = "";


PolytopeArea::usage = "";


Begin["`Private`"]


ColinearQ[pts_?MatrixQ] := MatrixRank[
  Join[Transpose[pts], {ConstantArray[1, Length@pts]}] // Transpose] <= 2;


RemoveColinear[pts_?MatrixQ] := 
  ReplaceRepeated[{
    {l___, a_, b_, c_, r___} :> {l, a, c, r} /; ColinearQ[{a, b, c}], 
    {a_, b_, f___, c_} :> {b, f, c} /; ColinearQ[{c, a, b}], 
    {a_, f___, b_, c_} :> {a, f, b} /; ColinearQ[{c, a, b}]
  }]@pts;


SyntaxInformation[DualPolytope] = {"ArgumentsPattern" -> {_}};

DualPolytope[pts_?MatrixQ] := {x, y} // 
  ReplaceAll@Solve[And @@ ({x, y}.#1 >= -1 &) /@ pts, {x, y}, Integers];


SyntaxInformation[PolytopeVertices] = {"ArgumentsPattern" -> {_}};

PolytopeVertices[pts_?MatrixQ] := Module[
  {furthest, argGrouped, vertices},
  argGrouped = DeleteCases[pts, {0, 0}] // 
    GroupBy@Apply[Mod[Arg[#1 + I #2], 2 Pi] &] // KeySortBy[N];
  furthest = First@MaximalBy[#, Abs, 1] & /@ argGrouped // Values;
  vertices = Select[furthest, 
    !PossibleZeroQ[PolygonAngle[Polygon@furthest, #] - Pi] &]
]


SyntaxInformation[PolytopePlot] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};

PolytopePlot[pts_?MatrixQ, opts: OptionsPattern[Graphics] ] := 
  Module[{vert, other},
    vert = PolytopeVertices[pts];
    other = DeleteCases[pts, Alternatives@@(vert~Join~{{0, 0}})];
    Graphics[{
      {EdgeForm[{Thick, Black}], FaceForm[Transparent], Polygon@vert},
      {FaceForm[Black], Disk[#, 0.15] & /@ vert},
      {EdgeForm[{Thick, Black}], FaceForm[Yellow], Disk[#, 0.12] & /@ other},
      {EdgeForm[{Thick, Black}], FaceForm@Lighter[Red, 0.6], Disk[{0, 0}, 0.12]}
    }, opts]
  ];


SyntaxInformation[PolytopeArea] = {"ArgumentsPattern" -> {_}};

PolytopeArea[pts_?MatrixQ] := Area@Polygon@PolytopeVertices[pts];


With[{syms = Names["QuiverGaugeTheory`Polytope`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
]

End[]

EndPackage[]
