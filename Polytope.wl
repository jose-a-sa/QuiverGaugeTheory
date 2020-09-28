(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Polytope`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Main`"
}]


PolytopeQ::usage = "";


DualPolytope::usage = "";


PolytopeVertices::usage = "";


PolytopePlot::usage = "";


PolytopeArea::usage = "";


pqWeb::usage = "";


pqWebQ::usage = "";


pqWebPlot::usage = "";


MixedBoundaryInternalMesh::usage = "";



Begin["`Private`"]


SyntaxInformation[PolytopeQ] = {"ArgumentsPattern" -> {_}};

PolytopeQ[pts_?MatrixQ] := 
  MatchQ[pts, {{__?ExactNumberQ} ..}];
PolytopeQ[_] := False;


SyntaxInformation[PolytopeVertices] = {"ArgumentsPattern" -> {_}};

PolytopeVertices[pts_?PolytopeQ] :=
  Module[{boundary, hull, sortF, extremal},
    sortF[{x_, y_}] := Apply[N@ArcTan[#1 - x, #2 - y] &];
    hull = First /@ Nearest[pts, MeshCoordinates@ConvexHullMesh@pts];
    boundary = SortBy[hull, sortF[RegionCentroid@Point@hull] ];
    extremal = AssociationMap[ColinearQ,
        Partition[boundary, 3, 1, {1, 1}]
      ] // KeyMap[#[[2]] &] // DeleteCases[True] // Keys;
    {extremal, Complement[pts, boundary], boundary}
  ];


SyntaxInformation[ReflexivePolytopeQ] = {"ArgumentsPattern" -> {_}};

ReflexivePolytopeQ[pts_?PolytopeQ] := 
  Length[ PolytopeVertices[pts][[2]] ] == 1;


SyntaxInformation[DualPolytope] = {"ArgumentsPattern" -> {_}};

DualPolytope[pts_?PolytopeQ] := 
  Module[{x, c0, p},
    c0 = PolytopeVertices[pts][[2, 1]];
    p = Array[x, {Length@c0}];
    p /. Solve[And @@ (p.(#1 - c0) >= -1 &) /@ pts, p, Integers]
  ];


SyntaxInformation[PolytopePlot] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};

PolytopePlot[pts_?PolytopeQ, opts: OptionsPattern[Graphics] ] := 
  Module[{extremal, internal, boundary},
    {extremal, internal, boundary} = PolytopeVertices[pts];
    Graphics[{
      {EdgeForm[{Thick, Black}], FaceForm[Transparent], Polygon@extremal},
      {FaceForm[Black], Disk[#, 0.15] & /@ extremal},
      {EdgeForm[{Thick, Black}], FaceForm[Yellow], 
        Disk[#, 0.12] & /@ Complement[boundary, extremal]},
      {EdgeForm[{Thick, Black}], FaceForm@Lighter[Red, 0.6], 
        Disk[#, 0.12] & /@ internal}
    }, opts]
  ];


SyntaxInformation[PolytopeArea] = {"ArgumentsPattern" -> {_}};

PolytopeArea[pts_?PolytopeQ] := 
  Module[{boundary, areas},
    boundary = Last@PolytopeVertices[pts];
    areas = Area@*Polygon /@ NestList[
      RotateLeft[#, 1] &, boundary, Length@boundary - 1
    ] // DeleteCases[ 0 | Undefined ];
    If[ Equal@@areas, First@areas, Undefined]
  ];


SyntaxInformation[pqWeb] = {"ArgumentsPattern" -> {_, _.}};

pqWeb[pts_?PolytopeQ, meshF_ : DelaunayMesh] :=
  Module[{V, B, l, trig, rotateLines, coordRules, edgeRules, 
      edgeFaceConnectivity, bdEdgesVectorsRules, intEdgesVectorsRules, eqs,
      basePtsRules, sol, loopEqs, loopVars, loopSol, baseSol, finalSol},
    {V, B, l} = {\[FormalCapitalV], \[FormalCapitalB], \[FormalL]};
    trig = meshF[pts];
    rotateLines = NormalizeGCD@*RotationTransform[-Pi/2]@*Apply[Subtract];
    coordRules = Rule @@@ IndexedList[ Rationalize@MeshCoordinates@trig ];
    edgeRules = Rule @@@ IndexedList[ Identity @@@ MeshCells[trig, 1] ];
    edgeFaceConnectivity = KeyValueMap[Rule]@GroupBy[
      EdgeList@MeshConnectivityGraph[trig, {1, 2}, 1],
      ReplaceAll[edgeRules]@*Last@*First -> Last@*Last
    ];
    bdEdgesVectorsRules = Association@MapIndexed[
      DirectedEdge[First@#1, V@First@#2] -> rotateLines@Last@#1 &,
      Cases[edgeFaceConnectivity,
        HoldPattern[l_ -> {f_}] :> {B[f], Reverse[l]/.coordRules}]
    ];
    intEdgesVectorsRules = Association@Map[
      (UndirectedEdge @@ First[#]) -> rotateLines@Last@# &,
      Cases[edgeFaceConnectivity, 
        HoldPattern[l_ -> {i_, f_}] :> {{B[i], B[f]}, (l/.coordRules)}]
    ];
    eqs = intEdgesVectorsRules // 
      KeyValueMap[(Subtract @@ #1) == (Identity @@@ l @@ #1) #2 &];
    basePtsRules = Array[ B[#] -> {B[#, 1], B[#, 2]} &, 
      {Max@Values@edgeFaceConnectivity}];
    sol = First@Solve[eqs /. basePtsRules];
    loopEqs = Select[sol, MatchQ[ HoldPattern[Rule][ l[__], _] ] ];
    loopVars = UniqueCases[loopEqs, l[__] ];
    loopSol = If[ Length@loopEqs > 0, 
      Last@Minimize[ {Plus @@ loopVars, 
        Join[Equal @@@ loopEqs, Thread[loopVars > 0] ]},
        loopVars, Integers], 
      {}
    ];
    baseSol = Select[sol /. loopSol, MatchQ[ HoldPattern[Rule][B[__], _] ] ];
    finalSol = basePtsRules // ReplaceAll[baseSol] // 
      ReplaceAll[{B[1, _] -> 0, l[__] -> 1}];
    {Keys@Union[intEdgesVectorsRules, bdEdgesVectorsRules], 
      Union[finalSol, KeyValueMap[Last@#1 -> #2 &]@bdEdgesVectorsRules]}
 ];


SyntaxInformation[pqWebQ] = {"ArgumentsPattern" -> {_}};

pqWebQ[expr_] := 
  MatchQ[expr, {
    {(UndirectedEdge[\[FormalCapitalB][_], \[FormalCapitalB][_] ] |
      DirectedEdge[\[FormalCapitalB][_], \[FormalCapitalV][_] ]) .. },
    {HoldPattern[Rule][(\[FormalCapitalB]|\[FormalCapitalV])[_], _] ..}
  }];


SyntaxInformation[pqWebPlot] = {"ArgumentsPattern" -> {_, _.}};

pqWebPlot[pts_?PolytopeQ, meshF_ : DelaunayMesh] :=
  pqWebPlot[ pqWeb[pts, meshF], meshF];
pqWebPlot[pq_?pqWebQ, meshF_ : DelaunayMesh] :=
  Module[{pqWebGraph, rules},
    {pqWebGraph, rules} = pq;
    gr = pqWebGraph // ReplaceAll[rules] // 
      ReplaceAll[ UndirectedEdge[i_, j_] :> Line[{i,j}] ] //
      ReplaceAll[ DirectedEdge[i_, j_] :> HalfLine[i,j] ];
    Graphics[gr, PlotRangePadding -> 2, Frame -> True, FrameTicks -> None]
 ];


MixedBoundaryInternalMesh[pts_?PolytopeQ, internalMeshF_ : DelaunayMesh] := 
  Module[{extremal, boundary, internal, 
      intLines0, intLines, emptyIntersectionQ, cells0, cells1, cells2}, 
    {extremal, internal, boundary} = PolytopeVertices[pts];
    emptyIntersectionQ = MatchQ@Alternatives[
      Point[{(Alternatives @@ pts) ..}], 
      EmptyRegion[_] 
    ];
    intLines0 = Switch[Length@internal,
      1, {}, 2, {internal},
      _, Identity @@@ MeshCells[internalMeshF@internal, 1] //
        ReplaceAll@Thread[Range@Length@internal -> internal]
    ];
    intLines = Fold[
      If[emptyIntersectionQ@RegionIntersection[Line@#1, Line@#2],
        Append[#1, #2], #1] &,
      intLines0,
      SortBy[ Tuples[{internal, boundary}], Norm@*Apply[Subtract] ]
    ];
    cells0 = Point /@ pts;
    cells1 = Line /@ Join[intLines, Partition[boundary, 2, 1, {1, 1}] ];
    cells2 = Flatten@Table[
      SubsetCases[cells1,
        {Line[{OrderlessPatternSequence[l[[1]], x_]}], 
          Line[{OrderlessPatternSequence[l[[2]], x_]}]} :> 
            Polygon[{l[[1]], x, l[[2]]}] /; ! ContainsAny[{x}, l] 
      ], {l, First /@ cells1} ] // DeleteDuplicatesBy[RegionCentroid];
    MeshRegion[pts, {cells0, cells1, cells2} // 
      ReplaceAll@Thread[pts->Range@Length@pts] 
    ]
  ]

End[]

EndPackage[]
