(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Polytope`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Main`"
}]


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

PolytopeVertices[pts_?MatrixQ] :=
  Module[{sorted, hull, sortF, vert},
    hull = (First@Nearest[pts, #] &) /@ MeshCoordinates@ConvexHullMesh[pts];
    sortF[{x_, y_}] := (\[Pi] - 1. ArcTan[#1 - x, #2 - y] &);
    sorted = hull // SortBy[ Apply@sortF[RegionCentroid@Polygon@hull] ];
    vert = Select[sorted,!PossibleZeroQ[PolygonAngle[Polygon@sorted, #] - Pi] &];
    {vert, hull}
  ];


SyntaxInformation[PolytopePlot] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};

PolytopePlot[pts_?MatrixQ, opts: OptionsPattern[Graphics] ] := 
  Module[{vert, hull, inside},
    {vert, hull} = PolytopeVertices[pts];
    Graphics[{
      {EdgeForm[{Thick, Black}], FaceForm[Transparent], Polygon@vert},
      {FaceForm[Black], Disk[#, 0.18] & /@ vert},
      {EdgeForm[{Thick, Black}], FaceForm[Yellow], 
        Disk[#, 0.12] & /@ Complement[hull, vert]},
      {EdgeForm[{Thick, Black}], FaceForm@Lighter[Red, 0.6], 
        Disk[#, 0.12] & /@ Complement[pts, hull]}
    }, opts]
  ];


SyntaxInformation[PolytopeArea] = {"ArgumentsPattern" -> {_}};

PolytopeArea[pts_?MatrixQ] := Area@Polygon@Last@PolytopeVertices[pts];


End[]

EndPackage[]
