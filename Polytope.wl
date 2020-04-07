(* ::Package:: *)

(* Wolfram Language Package *)

BeginPackage["QuiverGaugeTheory`Polytope`", {"QuiverGaugeTheory`Main`"}]
(* Exported symbols added here with SymbolName::usage *)  


Unprotect["QuiverGaugeTheory`Polytope`*"];
ClearAll["QuiverGaugeTheory`Polytope`*"];


DualPolytope::usage = "";


PolytopeVertices::usage = "";


PolytopePlot::usage = "";


PolytopeArea::usage = "";


Begin["`Private`"] (* Begin Private Context *)


ColinearQ[pts_?MatrixQ] := MatrixRank[
  Join[Transpose[pts], {ConstantArray[1, Length@pts]}] // Transpose] <= 2;


RemoveColinear[pts_?MatrixQ] := 
  ReplaceRepeated[{
    {l___, a_, b_, c_, r___} :> {l, a, c, r} /; ColinearQ[{a, b, c}], 
    {a_, b_, f___, c_} :> {b, f, c} /; ColinearQ[{c, a, b}], 
    {a_, f___, b_, c_} :> {a, f, b} /; ColinearQ[{c, a, b}]
  }]@pts;


DualPolytope[pts_?MatrixQ] := {x, y} // 
  ReplaceAll@Solve[And @@ ({x, y}.#1 >= -1 &) /@ pts, {x, y}, Integers];


PolytopeVertices[pts_?MatrixQ] := Module[
  {furthest, argGrouped, vertices},
  argGrouped = DeleteCases[pts, {0, 0}] // 
    GroupBy@Apply[Mod[Arg[#1 + I #2], 2 Pi] &] // KeySortBy[N];
  furthest = First@MaximalBy[#, Abs, 1] & /@ argGrouped // Values;
  vertices = Select[furthest, 
    !PossibleZeroQ[PolygonAngle[Polygon@furthest, #] - Pi] &]
]


PolytopePlot[pts_?MatrixQ, opts: OptionsPattern[Graphics] ] := 
  Block[{vert = PolytopeVertices[pts]}, 
    Graphics[{
      {EdgeForm[{Thick, Black}], FaceForm[Transparent], Polygon@vert},
      {FaceForm[Black], Disk[#, 0.15] & /@ vert},
      {EdgeForm[{Thick, Black}], FaceForm[Yellow], Disk[#, 0.12] & /@ 
        DeleteCases[Alternatives@@(vert~Join~{{0, 0}})]@pts},
      {EdgeForm[{Thick, Black}], FaceForm@Lighter[Red, 0.6], Disk[{0, 0}, 0.12]}
    }, opts]
  ];


PolytopeArea[pts_?MatrixQ] := Area@Polygon@PolytopeVertices[pts];


With[{syms = Names["QuiverGaugeTheory`Polytope`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
]

End[] (* End Private Context *)

EndPackage[]
