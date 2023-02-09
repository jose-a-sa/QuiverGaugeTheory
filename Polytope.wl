(* ::Package:: *)

Unprotect["QuiverGaugeTheory`Polytope`*"];
ClearAll["QuiverGaugeTheory`Polytope`*"];


BeginPackage["QuiverGaugeTheory`Polytope`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`",
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Tiling`"
}]


PolytopeQ::usage = "";
ToricDiagramQ::usage = "";
PolytopeTriangulationQ::usage = "";
PolytopeTriangulationCellsQ::usage = ""; 
PolytopeTriangulationEdgesQ::usage = "";
PolytopeVertices::usage = "";
ReflexivePolytopeQ::usage = "";
DualPolytope::usage = "";
NormalizePolytope::usage = "";
FastForward::usage = "";
ToricDiagram::usage = "";
ZigZagPerfectMatchings::usage = "";
ZigZagData::usage = "";
PolytopePlot::usage = "";
PolytopeArea::usage = "";
PolytopeCentroid::usage = "";
TriangulationFlips::usage = "";
PolytopeTriangulationsGraph::usage = "";
PolytopeTriangulations::usage = "";
pqWebFromTriagulation::usage = "";
pqWebFromTriagulationQ::usage = "";
pqWebReduced::usage = "";
pqWebResolve::usage = "";
pqWebResolvedQ::usage = "";
pqWebCycle::usage = "";
pqWebPlot::usage = "";
AMaximization::usage = "";


$ExtremalPerfectMatchingVar::usage = "";
$BoundaryPerfectMatchingVars::usage = "";
$InternalMatchingVars::usage = "";
$PerfectMatchingVars::usage = "";
$FayetIliopoulosVar::usage = "";


Begin["`Private`"]


$ExtremalPerfectMatchingVar = ToExpression["\[FormalP]"];
$InternalMatchingVars =  
  Alternatives @@ ToExpression@CharacterRange["\[FormalS]", "\[FormalZ]"];
$BoundaryPerfectMatchingVars = 
  Alternatives @@ ToExpression@CharacterRange["\[FormalF]", "\[FormalO]"];
$FayetIliopoulosVar = ToExpression["\[FormalXi]"];

$PerfectMatchingVars := Join[
  Alternatives@$ExtremalPerfectMatchingVar, 
  $InternalMatchingVars,
  $BoundaryPerfectMatchingVars];


SyntaxInformation[PolytopeQ] = {"ArgumentsPattern" -> {_}};
PolytopeQ[pts : {{_Integer,_Integer} ..}] :=
  Length@DeleteDuplicates[pts] > 2;
PolytopeQ[_] := False;
SetAttributes[PolytopeQ, {Protected, ReadProtected}];


SyntaxInformation[ToricDiagramQ] = {"ArgumentsPattern" -> {_}};
ToricDiagramQ[td : KeyValuePattern[{}] ] :=
  ToricDiagramQ[Values@Association@td];
ToricDiagramQ[pts_?PolytopeQ] :=
  AllTrue[(Count[pts, #] &) /@ First@PolytopeVertices@pts, #1 === 1 &];
ToricDiagramQ[_] := False;
SetAttributes[ToricDiagramQ, {Protected, ReadProtected}];


SyntaxInformation[PolytopeTriangulationQ] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationQ[m_MeshRegion] := And[
    PolytopeQ@Rationalize@MeshCoordinates[m],
    Equal @@ Map[PolytopeArea@*First, MeshCells[m,2] /. MapIndexed[
      First@#2 ->#1 &, Rationalize@MeshCoordinates@m] 
    ]
  ];
PolytopeTriangulationQ[_] := False;
SetAttributes[PolytopeTriangulationQ, {Protected, ReadProtected}];


SyntaxInformation[PolytopeTriangulationCellsQ] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationCellsQ[
  {{Point[_Integer]...}, {Line[{__Integer}]...}, {Polygon[{__Integer}]...}}
] := True;
PolytopeTriangulationCellsQ[_] := False;
SetAttributes[PolytopeTriangulationCellsQ, {Protected, ReadProtected}];


SyntaxInformation[PolytopeTriangulationEdgesQ] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationEdgesQ[{Line[{_,_}]...}] := True;
PolytopeTriangulationEdgesQ[{UndirectedEdge[_,_]...}] := True;
PolytopeTriangulationEdgesQ[{List[_,_]...}] := True;
PolytopeTriangulationEdgesQ[_] := False;
SetAttributes[PolytopeTriangulationEdgesQ, {Protected, ReadProtected}];


SyntaxInformation[PolytopeVertices] = {"ArgumentsPattern" -> {_}};
PolytopeVertices[pts_?PolytopeQ] :=
  Module[{hull, c0, sortF, ex, bd, ex1},
    sortF[{x_, y_}] := Apply[N@ArcTan[#1-x,#2-y] &];
    hull = ConvexHullMesh[pts];
    c0 = RegionCentroid[hull];
    bd = SortBy[sortF@c0]@Select[
      DeleteDuplicates@pts,
      RegionMember@RegionBoundary@hull
    ];
    ex = Extract[2] /@ Select[
      Partition[bd, 3, 1, {1, 1}],
      Not@*CollinearQ];
    ex1 = First@MinimalBy[Identity]@ex;
    {
      NestWhile[RotateLeft, ex, UnequalTo[ex1]@*First],
      Complement[pts, bd],
      NestWhile[RotateLeft, bd, UnequalTo[ex1]@*First]
    }
  ];
SetAttributes[PolytopeVertices, {Protected, ReadProtected}];


SyntaxInformation[ReflexivePolytopeQ] = {"ArgumentsPattern" -> {_}};
ReflexivePolytopeQ[pts_?PolytopeQ] := 
  Length[ PolytopeVertices[pts][[2]] ] == 1;
ReflexivePolytopeQ[_] := False;
SetAttributes[ReflexivePolytopeQ, {Protected, ReadProtected}];


SyntaxInformation[DualPolytope] = {"ArgumentsPattern" -> {_}};
DualPolytope[pts_?ReflexivePolytopeQ] := 
  Module[{x, c0, p},
    c0 = Round@Mean@PolytopeVertices[pts][[2]];
    p = Array[x, {Length@c0}];
    p /. Solve[And @@ (p.(#1 - c0) >= -1 &) /@ pts, p, Integers]
  ];
SetAttributes[DualPolytope, {Protected, ReadProtected}];


SyntaxInformation[NormalizePolytope] = {"ArgumentsPattern" -> {_}};
NormalizePolytope[pt_?PolytopeQ] :=
  Module[{c0, sortV, glMs, newP, polyAngle, min, rules, vert, newP2},
    vert = PolytopeVertices[pt];
    c0 = Round@If[vert[[2]] == {}, PolytopeCentroid[pt], vert[[2]]//Mean ];
    newP = Map[# - c0 &, pt];
    polyAngle[pts_?MatrixQ] := Association[
      (#2 -> VectorAngle[#1 - #2, #3 - #2] &) @@@ Partition[RotateRight@pts, 3, 1, {1, 1}]
    ];
    sortV = Block[{ex, int, bd, ang},
      {ex, int, bd} = PolytopeVertices[#];
      ang = polyAngle[ex];
      {
        Total[EuclideanDistance @@@ Partition[ex, 2, 1, {1, 1}] ], 
        Abs@Apply[Subtract]@MinMax@Values@ang,
        Total@Map[z |-> z.z, #],
        {-1, 1}.MinMax[First /@ bd],
        -Values@KeySort@CountsBy[bd, First], 
        -Values@KeySort@CountsBy[bd, Last],
        -KeyValueMap[#2*{Last@#1,First@#1} &]@KeySortBy[ang, Last]
      }
    ] &;
    glMs = Select[
      {{#1, #2}, {#3, #4}} & @@@ Tuples[Range[-2, 2], 4],
      Det[#]^2 == 1 &
    ];
    min = MinimalBy[N]@AssociationMap[
      Apply[sortV[#2] &], 
      Table[{m, Map[m.# &, newP]}, {m, glMs}]
    ];
    rules = KeyMap[
      DeleteCases[
        Thread[newP -> Last@#], 
        HoldPattern[Rule][x_, x_]
      ] &, min];
    newPt = newP /. First@Keys@KeySortBy[rules, Length];
    vert = PolytopeVertices[newPt];
    c0 = Floor@If[vert[[2]] == {}, PolytopeCentroid[newPt], vert[[2]]//Mean];
    Map[# - c0 &, newPt]
  ];
SetAttributes[NormalizePolytope, {Protected, ReadProtected}];


SyntaxInformation[FastForward] = {"ArgumentsPattern" -> {_}};
FastForward[w_?ToricPotentialQ] :=
  Module[{d, pMat, nF, nPM, nG, barReduce, qDb, qD, qF, q, gt},
    pMat = PerfectMatchingMatrix[w];
    d = QuiverIncidenceMatrix[w]/.{2->0};
    {nF, nPM} = Dimensions[pMat];
    nG = First@Dimensions[d];
    qF = NullSpace[pMat];
    qDb = SolveMatrixLeft[Transpose[pMat], d];
    barReduce = Transpose@Join[
      {Table[-1, {nG-1}]}, 
      IdentityMatrix[nG-1] 
    ];
    qD = barReduce.qDb;
    q = Join[qF, qD];
    gt = NullSpace[q];
    If[StrictlyCoplanarQ@Transpose@gt,
      gt = Join[Most@gt, {Table[1, {nPM}]}],
      Message[FastForward::notcoplanar]
    ];
    <|"Gt" -> gt, "QF" -> qF, "QD" -> qD, "QDb" -> qDb|>
  ];
FastForward::notcoplanar = "Resulting polytope is not strictly coplanar.";
SetAttributes[FastForward, {Protected, ReadProtected}];


SyntaxInformation[ToricDiagram] = {"ArgumentsPattern" -> {_,_.}};
ToricDiagram[w_?ToricPotentialQ, m_?MatrixQ ] :=
  Block[{mat},
    mat = If[Dimensions@m =!= {2,2} || PossibleZeroQ@Det@m, 
      IdentityMatrix[2], m];
    Map[ mat.# &, ToricDiagram[w] ]
  ];
ToricDiagram[w_?ToricPotentialQ] :=
  Module[{ff, pt, ex, int, bd, nex, posEx, posInt, 
      posNEx, exVar, intVar, nexVar, sortedPM},
    ff = FastForward[w];
    pt = NormalizePolytope@Transpose@Most@First@ff;
    {ex, int, bd} = PolytopeVertices[pt];
    nex = Complement[bd, ex];
    {posEx, posInt, posNEx} = {
      FirstPosition[pt, #] & /@ ex,
      Position[pt, #] & /@ int,
      Position[pt, #] & /@ nex};
    exVar = $ExtremalPerfectMatchingVar;
    intVar = Take[List @@ $InternalMatchingVars, Length@int];
    nexVar = Take[List @@ $BoundaryPerfectMatchingVars, Length@nex];
    sortedPM = Values@Sort@Flatten@MapThread[
      MapThread[Rule, {#2, Thread@Subscript[#1, Range@Length@#2]}] &,
      {Join[{exVar}, nexVar, intVar], Join[{posEx}, posNEx, posInt]}
    ];
    AssociationThread[sortedPM, pt]
  ];
SetAttributes[ToricDiagram, {Protected, ReadProtected}];


(* ZigZagPerfectMatchings[w_?ToricPotentialQ] :=
  Module[{f, zzs, td, pms, bd, pmPairs},
    f = FieldCases[w];
    zzs = KeyValueReverse@AssociationMap[
      Sort@*Apply[List], ZigZagPaths@w];
    td = ToricDiagram[w];
    bd = Last@PolytopeVertices[Values@td];
    pms = Normal@AssociationThread[Keys@td,
      DeleteCases[f^#, 1] & /@ Transpose@PerfectMatchingMatrix[w]
    ];
    pmPairs = Join @@ Map[Tuples,
      Partition[bd /. Normal@GroupBy[td, Identity, Keys], 2, 1, {1, 1}]
    ];
    KeyMap[Lookup[zzs, Key@Sort@#] &]@GroupBy[pmPairs,
      Apply[SymmetricDifference]@*ReplaceAll[pms]
    ]
  ] /; (PotentialEulerCharacteristic[w] == 0); *)
ZigZagPerfectMatchings[w_?ToricPotentialQ] :=
  Module[{td, pmm, pms, pmGroups, pmDiffs, altPatt, mesZZ},
    td = ToricDiagram[w];
    pmm = PerfectMatchingMatrix[w];
    pms = AssociationThread[Keys@td, 
      (DeleteCases[FieldCases[w]^#, 1] & /@ Transpose@pmm)];
    pmGroups = Last@PolytopeVertices[Values@td] /. 
      GroupBy[Normal@td, Last -> First];
    pmDiffs = Splice@*Tuples /@ Partition[pmGroups, 2, 1, {1, 1}];
    altPatt = Alternatives[{PatternSequence[1, -1] ..}, 
      {PatternSequence[-1, 1] ..}, {1, PatternSequence[-1, 1] ...}, 
      {PatternSequence[-1, 1] ..., -1}];
    mesZZ = Select[
      First@Values@Mesons[ CenterDot @@ SymmetricDifference[#1,#2] ],
      MatchQ[altPatt]@*ReplaceAll[ Join[ Thread[#1->1], Thread[#2->-1] ] ]@*Apply[List]
    ] & @@@ (pmDiffs /. pms);
    KeySelect[ZigZagPathQ@w]@GroupBy[
      Normal@Select[AssociationThread[pmDiffs, mesZZ], Length[#] == 1 &],
      First@*Last -> First
    ]
  ] /; (PotentialEulerCharacteristic[w] == 0);
ZigZagPerfectMatchings[w_?ToricPotentialQ] :=
  Null /; Message[ZigZagPerfectMatchings::gnotimpl, (2 - PotentialEulerCharacteristic[w])/2];
ZigZagPerfectMatchings::gnotimpl = "ZigZagPerfectMatchings not implemented for genus `1` models.";
SetAttributes[ZigZagPerfectMatchings, {Protected, ReadProtected}];


ZigZagData[w_?ToricPotentialQ] :=
  Module[{a, sl2Sol, amax, rch, td, zzs, pq, len, ops, normalSize},
    sl2Sol[{p_, q_}] := Array[a, {2, 2}] /. Last@Solve[
        Det@Array[a, {2, 2}] == 1 && Inverse[Transpose@Array[a, {2, 2}]].{p, q} == {-1, 0},
      Integers] /. {C[_] -> 0, a[__] -> 0};
    amax = Normal@Last@AMaximization[w];
    td = ToricDiagram[w];
    zzs = ZigZagPerfectMatchings[w];
    pq = Map[
      RotationTransform[Pi/2]@*Apply[Subtract]@*ReplaceAll[td]@*First,
      zzs];
    len = AssociationMap[Length, Keys@zzs];
    normalSize = Map[
      ReplaceAll@Normal@AssociationMap[
        Function[v, -Subtract @@ First@CoordinateBounds@Map[sl2Sol[v].# &, td]],
        Union@Values@pq
      ], pq];
    ops = AssociationMap[ZigZagOperators[w, #] &, Keys@zzs];
    rch = Map[
      First@*N@*ReplaceAll[amax]@*Abs@*ReplaceAll[CenterDot -> Plus], 
      ops];
    Merge[{pq, len, normalSize, ops, rch}, Identity]
  ];
SetAttributes[ZigZagData, {Protected, ReadProtected}];



Options[PolytopePlot] = Normal@Association@{
  Splice@Options[Graphics],
  ImageSize -> Small,
  PlotRange -> Automatic,
  GridLines -> None, 
  PlotRangePadding -> Scaled[0.1],
  GridLinesStyle -> 
  Directive[AbsoluteThickness[1], GrayLevel[0.75] ],
  "pqWeb" -> None,
  "pqWebStyle" -> Directive[Black, Thick, Arrowheads[0.085] ], 
  "pqWebArrowFunction" -> (Arrow[{Mean[#2], Mean[#2] + Normalize[#1]}, {0.2, -0.2}] &),
  "PolytopeCellLabel" -> None,
  "PolytopeCellLabelFunction" -> Automatic,
  "PolytopeCellStyle" -> Automatic,
  "PolytopeCellFunction" -> Automatic
};
$lineLabelAngle = (ArcTan @@ SelectFirst[
  {{1, -1}, {-1, 1}}.#, 
  NonNegative@*First, {1, 0}] &);
$polytopeCellLabelStyle = Directive[
  Background -> None, FontSize -> 12];
$polytopeCellStyle = Association@{
  "ExtremalPoints" -> Directive[EdgeForm[{Thickness[0.012], Black}], FaceForm[Black] ],
  "NonExtremalPoints" -> Directive[EdgeForm[{Thickness[0.012], Black}], FaceForm[Yellow] ],
  "InternalPoints" -> Directive[
    EdgeForm[{Thickness[0.012], Black}], 
    FaceForm[{Lighter[Red, 0.6]}] ],
  "InternalEdges" -> Directive[Thickness[0.012], Black],
  "BoundaryEdges" -> Directive[Thickness[0.015], Black],
  "Polygons" -> Directive[EdgeForm[None], FaceForm[None] ]
};
$polytopeCellFunction = Association@{
  "ExtremalPoints" -> (Disk[#1, 0.11] &),
  "NonExtremalPoints" -> (Disk[#1, 0.09] &),
  "InternalPoints" -> (Disk[#1, 0.09] &),
  "InternalEdges" -> (Line[#1] &),
  "BoundaryEdges" -> (Line[#1] &),
  "Polygons" -> (Polygon[#1] &)
};
$polytopeCellLabelFunction = Association@{
  "ExtremalPoints" -> (Text[#1, #2 + 0.2 #3, -#3] &),
  "NonExtremalPoints" -> (Text[#1, #2 + 0.15 #3, -#3] &),
  "InternalPoints" -> (Text[#1, #2 + 0.15 #3, -#3] &),
  "InternalEdges" -> (Rotate[
    Text[#1, #2 + 0.15 #3, -#3], $lineLabelAngle@#4] &),
  "BoundaryEdges" -> (Rotate[
    Text[#1, #2 + 0.15 #3, -#3], $lineLabelAngle@#4] &),
  "Polygons" -> (Text[#1, #2 + 0.15 #3, -#3] &)
};
PolytopePlot[td_?ToricDiagramQ, opts : OptionsPattern[PolytopePlot] ] :=
  Module[{trig, tdG, ex, in, bd, coord, optLbl, cellLbl, pattQ},
    tdG = PositionIndex[td];
    {ex, in, bd} = PolytopeVertices[Keys@tdG];
    coord = MapIndexed[#1 -> First[#2] &, Keys@tdG];
    trig = MeshRegion[Keys@tdG, 
      {{Map[Point, Join[bd, in] /. coord]}, {}, Polygon[bd /. coord]}];
    optLbl = OptionValue["PolytopeCellLabel"];
    pattQ = MatchQ@KeyValuePattern[{_ -> {(Subscript[$PerfectMatchingVars, _])..}}];
    cellLbl = Switch[optLbl,
      "PerfectMatchings" | Automatic,
      KeyMap[Point]@If[pattQ[tdG], Map[Last]@tdG,
        KeySelect[ FreeQ[Alternatives@@ex] ]@Map[Length]@tdG
      ],
      "Counts" | Automatic,
      KeyMap[Point]@KeySelect[ FreeQ[Alternatives@@ex] ]@Map[Length]@tdG,
      _, optLbl
    ];
    PolytopePlot[trig,
      "PolytopeCellLabel" -> cellLbl,
      Sequence @@ FilterRules[{opts}, Except["PolytopeCellLabel"] ]
    ]
  ];
PolytopePlot[trig_?PolytopeTriangulationQ, opts : OptionsPattern[PolytopePlot] ] :=
  Module[{remPrim, sortPrim, coord, cell, cellType, cellPts, ptsCells, cellGroups,
      ex, int, bd, lblOffsets, cellStyles, cellFuncs, cellLbls, cellLblFuncs,
      grPolyAssoc, grCellLblAssoc, grPoly, grLbls, grPQWeb, gr, bounds},
    remPrim = ReplaceAll[{
      Point[x : {__Integer}] :> {x},
      (Point | Line | Polygon)[x : {{__Integer} ..}] :> 
        RotateRight[x, FirstPosition[Ordering@x, 1, 1] - 1]}
    ];
    sortPrim = ReplaceAll[{
      (f: (Point | Line | Polygon))[x : {{__Integer} ..}] :> 
        f@RotateRight[x, FirstPosition[Ordering@x, 1, 1] - 1]}
    ];
    {coord, cell, cellType} = polytopePlotCellIndex[trig];
    cellPts = AssociationFlatten@Map[remPrim@*ReplaceAll[coord], cell, {2}];
    ptsCells = KeyValueReverse[cellPts];
    cellGroups = KeyValueMap[
      {Last@#1, remPrim@#2, sortPrim@#2, First@#1, {Last[#1][[1]], All}} &,
      AssociationFlatten[cellType]
    ];
    {ex, int, bd} = PolytopeVertices@Values@coord;
    lblOffsets = KeyMap[ReplaceAll@Normal@ptsCells]@Join[
      (Simplify@RotationTransform[-Pi/2]@Normalize[ 
        Normalize[#3-#2] + Normalize[#2-#1] ] &) @@@ AssociationThread[
          (List /@ bd), Partition[RotateRight@bd, 3, 1, {1, 1}] 
      ],
      AssociationThread[(List /@ int), Table[{-1, -1}/Sqrt[2], Length@int] ]
    ];
    cellStyles = polytopePlotCellOptions["PolytopeCellStyle", 
      Map[{} &]@$polytopeCellStyle, cellGroups, 
      Directive[Thickness[-1], PointSize[-1], EdgeForm[None], FaceForm[None] ], opts];
    cellFuncs = polytopePlotCellOptions["PolytopeCellFunction",
      $polytopeCellFunction, cellGroups, ({} &), opts];
    cellLbls = polytopePlotCellOptions["PolytopeCellLabel",
      Map[None &]@$polytopeCellStyle, cellGroups, None, opts];
    cellLblFuncs = polytopePlotCellOptions["PolytopeCellLabelFunction",
      $polytopeCellLabelFunction, cellGroups, ({} &), opts];
    If[AnyTrue[{cellStyles, cellFuncs, cellLbls, cellLblFuncs}, FailureQ], 
      Return[Null],
      cellLbls = Select[cellLbls, MatchQ@Except[None] ];
      cellLblFuncs = KeyTake[cellLblFuncs, Keys@cellLbls];
    ];
    grPolyAssoc = Merge[{
      ReplaceAll[{x:{__?NumericQ}} -> x] /@ cellPts, 
      cellStyles, 
      cellFuncs},
      Apply[{c, d, f} |-> {Splice@Flatten[{d}], f[c]}]
    ];
    grCellLblAssoc = Merge[{
      KeyValueMap[#1 -> parseCellLabel[#2, Lookup[lblOffsets, Key[#1], {0, 0}] ] &, cellLbls],
      KeyTake[Keys@cellLbls]@cellPts, 
      cellLblFuncs},
      Apply[ {lbl, prim, func} |-> func[First@lbl, Mean@prim, Last@lbl, prim] ]
    ];
    grPoly = Map[
      {$polytopeCellStyle@#, Keys@cellType@#} &,
      Reverse@Keys@cellType] /. Normal[grPolyAssoc];
    grLbls = {$polytopeCellLabelStyle, Values@grCellLblAssoc};
    grPQWeb = polytopePlotpqWeb[Values@coord, opts];
    gr = {grPoly, grLbls, grPQWeb};
    bounds = polytopePlotBounds[gr, opts];
    Graphics[gr, 
      Sequence @@ FilterRules[FilterRules[{opts}, Options@Graphics], 
        Except[{GridLines, GridLinesStyle, PlotRange, PlotRangePadding, ImageSize}]
      ],
      GridLines -> (Range @@@ bounds),
      GridLinesStyle -> OptionValue["GridLinesStyle"],
      PlotRange -> If[bounds === None, OptionValue["PlotRange"], bounds], 
      PlotRangePadding -> If[bounds === None, OptionValue["PlotRangePadding"], None],
      ImageSize -> OptionValue["ImageSize"]
    ]
  ];
PolytopePlot::opterr = "The value `1` is not a valid \"`2`\" option. \
Options should be a key-value pattern with keys of the form {dim,i}, \
prim[{p1,p2,...}], {p1,p2,...} or" <> StringRiffle[
  Map[(StringJoin["\"", #1, "\""] &), Keys@$polytopeCellLabelFunction], {" ",", ","."}];
SetAttributes[PolytopePlot, {Protected, ReadProtected}];


polytopePlotCellOptions[optN_, defOpt_, cellGroups_, noneDef_, opts : OptionsPattern[PolytopePlot] ] := 
  Module[{ptAltPatt, ptOrderPattSeq, optV, opt, replaceF},
    ptAltPatt = {__Integer} | HoldPattern[Alternatives][{__Integer} ..];
    ptOrderPattSeq = Replace[{
      {x : (ptAltPatt ..)} :> Sort[{x}],
      (f : Line | Polygon)[{x : (ptAltPatt ..)}] :> f[Sort@{x}]
    }];
    optV = OptionValue[optN];
    opt = Switch[optV,
      None | False,
      AssociationThread[{{0, All}, {1, All}, {2, All}}, noneDef],
      Automatic | True,
      Association[defOpt],
      KeyValuePattern[{}],
      ReplaceAll[(None | False) -> noneDef] /@ KeyMap[ptOrderPattSeq]@Association[optV],
      _, $Failed
    ];
    If[FailureQ@opt, 
      Message[PolytopePlot::opterr, optV, optN]; Return[opt]
    ];
    replaceF = Block[{ruleAuto, ruleFixSty},
      ruleAuto = (True | Automatic) -> Lookup[defOpt, #4];
      ruleFixSty = Directive[x__] :> Directive[Flatten@{x}];
      Map[k |-> Lookup[opt, Key[k], k], 
        {#1, #2, #3, #4, #5} 
      ] /. ruleAuto /. ruleFixSty
    ] &;
    Association[(#1 -> (If[# === {}, {}, First@#] &)@SelectFirst[
        Transpose[{replaceF[##], {##}}], Apply[UnsameQ], 
        Lookup[defOpt, {#4, #4}]
      ] &) @@@ cellGroups]
  ];


polytopePlotCellIndex[trig_] :=
  Module[{coord, cell, cellC, ex, in, bd, nex, cellType, bdEdgeC},
    coord = (AssociationThread[Range[Length@#], #] &)@Rationalize@MeshCoordinates[trig];
    cell = Map[AssociationThread[Range[Length@#1], #1] &,
      AssociationMap[ MeshCells[trig, #] &, Range[0, 2] ]
    ];
    cellC = Map[ReplaceAll[coord], cell, {2}];
    {ex, in, bd} = PolytopeVertices[Values@coord];
    nex = Complement[bd, ex];
    cellType = <||>;
    AppendTo[cellType, AssociationThread[
        {"ExtremalPoints", "NonExtremalPoints", "InternalPoints"},
        (KeyMap[{0, #} &]@Select[cellC[0], 
          MatchQ@Point[Alternatives@@#] ] &) /@ {ex, nex, in}
      ]
    ];
    bdEdgeC = Keys@Select[Length[#] == 1 &]@GroupBy[
      EdgeList@MeshConnectivityGraph[trig, {2, 1}], Last -> First];
    AppendTo[cellType, <|
      "InternalEdges" -> KeyDrop[KeyMap[{1, #} &]@cellC[1], bdEdgeC],
      "BoundaryEdges" -> KeyTake[KeyMap[{1, #} &]@cellC[1], bdEdgeC],
      "Polygons" -> KeyMap[{2, #} &]@cellC[2]|>
    ];
    {coord, cell, cellType}
  ];


parseCellLabel[lbl_, def_ : {0, 0}] :=
  Module[{tblrRule, placedRule},
    tblrRule = {
      Left -> {-1, 0}, Right -> {1, 0}, 
      Top -> {0, 1}, Bottom -> {0, -1},
      Center | Automatic -> {0, 0}
    };
    placedRule = Switch[#,
      Left | Right | Top | Bottom | Center | Automatic,
      # /. tblrRule,
      {_?NumericQ, _?NumericQ}, #,
      None | False, {0, 0},
      _, def
    ] &;
    Apply[Placed[lbl /. #2, placedRule@#1] &,
      (First[#, {def, {}}] &)@Cases[lbl, 
        Placed[x_, p_] :> {p, Placed[x, p] -> x}, 
      {0, Infinity}]
    ]
  ];


polytopePlotpqWeb[pt_, opts : OptionsPattern[PolytopePlot] ] :=
  Module[{getOpt, remV, remNeg, pqVec, pqAssoc, n, pqW, 
      style, arrowF, arrowG, defStyle},
    getOpt[o_] := OptionValue[o] // If[MatchQ[#, Automatic],
      OptionValue[PolytopePlot, Options@PolytopePlot, o], #] &;
    remV = ReplaceAll[\[FormalCapitalV] -> Identity];
    {pqVec, pqAssoc} = KeyMap[remV] /@ pqWebReduced[pt];
    n = Length@pqVec;
    remNeg = ReplaceAll[i_?Negative :> i + n + 1];
    pqW = remV@OptionValue["pqWeb"] // Switch[#,
      Automatic | All | True, Range[n],
      _List, Union[remNeg@#],
      _, {}] & // Select@MatchQ[i_Integer /; 1<=i<=n];
    defStyle = OptionValue[PolytopePlot, Options@PolytopePlot, "pqWebStyle"];
    style = getOpt["pqWebStyle"] // Switch[#,
      KeyValuePattern[{}],
      Directive /@ KeyMap[remNeg]@Association@#,
      {(_Directive | {__}) ..}, 
      AssociationThread[Range@Length@#, Apply[Directive]@*Normal /@ #],
      _, AssociationThread[Range@n, Directive@#]
    ] & // KeySelect@MatchQ[i_Integer /; 1<=i<=n];
    arrowF = getOpt["pqWebArrowFunction"];
    arrowG = Merge[{pqVec, pqAssoc}, Apply@arrowF];
    {defStyle, Values@Merge[KeyTake[pqW] /@ {arrowG, style}, Reverse]}
  ];


polytopePlotBounds[gr_, opts : OptionsPattern[PolytopePlot] ] :=
  Module[{minBounds, minBoundsF, grid, allPatt},
    minBounds = {Floor[Min@#1], Ceiling[Max@#2]} & @@@ 
      Transpose[RegionBounds /@ Cases[gr, _?RegionQ, Infinity], {3, 1, 2}];
    minBoundsF = MapThread[
      Apply[{Min[#1], Max[#2]} &]@*Transpose@*List, 
      {#, minBounds}
    ] &;
    grid = OptionValue["GridLines"];
    allPatt = (All | Automatic | True);
    Switch[grid,
      allPatt | {allPatt, allPatt}, minBounds,
      {{bx_, tx_}, {by_, ty_}} /; (tx >= bx) && (ty >= by) && MatchQ[{bx, tx, by, ty}, {__Integer}],
      minBoundsF@grid,
      {allPatt, {b_, t_}} /; (t >= b) && MatchQ[{b, t}, {__Integer}],
      minBoundsF@{minBounds[[1]], grid},
      {{b_, t_}, allPatt} /; (t >= b) && MatchQ[{b, t}, {__Integer}],
      minBoundsF@{grid, minBounds[[2]]},
      {b_, t_} /; (t >= b) && MatchQ[{b, t}, {__Integer}],
      minBoundsF@Table[grid, {2}],
      _, None
    ]
  ];


SyntaxInformation[PolytopeArea] = {"ArgumentsPattern" -> {_}};
PolytopeArea[pt_?PolytopeQ] := 
  Module[{xs, ys},
    {xs, ys} = Transpose@First@PolytopeVertices[pt];
    Abs@Total[xs RotateLeft[ys] - RotateLeft[xs] ys]/2
  ];
SetAttributes[PolytopeArea, {Protected, ReadProtected}];


SyntaxInformation[PolytopeCentroid] = {"ArgumentsPattern" -> {_}};
PolytopeCentroid[pt_?PolytopeQ] :=
  Module[{xs, ys, as, cx, cy},
    {xs, ys} = Transpose@First@PolytopeVertices[pt];
    as = (xs RotateLeft[ys] - RotateLeft[xs] ys)/2;
    cx = Total[(xs + RotateLeft[xs]) as]/3;
    cy = Total[(ys + RotateLeft[ys]) as]/3;
    {cx, cy}/Abs[Total@as]
  ];
SetAttributes[PolytopeCentroid, {Protected, ReadProtected}];


SyntaxInformation[TriangulationFlips] = {"ArgumentsPattern" -> {_}};
TriangulationFlips[trig_MeshRegion] :=
  Module[{pts, edges, faces, flipablePairQ, fcPairs, fcPairsEdge, fcPairsEdgeNew,
      facesFlipR, edgesFlipR, facesTree, edgesTree},
    pts = MapIndexed[First@#2 -> #1 &, Rationalize@MeshCoordinates@trig];
    edges = Map[Sort, MeshCells[trig, 1], {0, 2}];
    faces = MeshCells[trig, 2];
    flipablePairQ[pair_] := 
      (ContainsExactly[Rationalize@MeshCoordinates@ConvexHullMesh@#, #] &)[
        Apply[Union, First /@ (faces[[pair]]/.pts)]
      ];
    fcPairs = Select[
      List @@@ Map[Last, EdgeList@MeshConnectivityGraph[trig, 2], {2}],
      flipablePairQ
    ];
    fcPairsEdge = KeyMap[faces[[#]] &]@AssociationMap[
      Line[ Intersection @@ Map[First, faces[[#1]], {1}] ] &,
      fcPairs
    ];
    fcPairsEdgeNew = Association@KeyValueMap[
      {fcs, e} |-> With[
        {newL = Flatten@Map[DeleteCases[Alternatives @@ First@e]@*First, fcs]},
        Map[Polygon@Append[newL, #] &, First@e] -> Line@newL], 
      fcPairsEdge];
    facesFlipR = AssociationThread[Keys@fcPairsEdge, Keys@fcPairsEdgeNew];
    edgesFlipR = AssociationThread[Values@fcPairsEdge, Values@fcPairsEdgeNew];
    facesTree = Map[Sort, Union[DeleteCases[faces, Alternatives @@ #1], #2], 
      {0, 2}] & @@@ Normal[facesFlipR];
    edgesTree = Map[Sort, Union[DeleteCases[edges, #1], {#2}], 
      {0, 2}] & @@@ Normal[edgesFlipR];
    MapThread[
      MeshRegion[Values@pts, {Point /@ Keys@pts, #1, #2}] &,
      {edgesTree, facesTree}
    ]
  ];
SetAttributes[TriangulationFlips, {Protected, ReadProtected}];


SyntaxInformation[PolytopeTriangulationsGraph] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationsGraph[td: KeyValuePattern[{}]?ToricDiagramQ] :=
  PolytopeTriangulationsGraph[Values@td];
PolytopeTriangulationsGraph[pt_?PolytopeQ] :=
  Module[{m0, trigI, graph0, graph},
    m0 = DelaunayMesh[pt];
    trigI = MeshRegion[Rationalize@MeshCoordinates@m0, {
      MeshCells[m0, 0], 
      Map[Sort, MeshCells[m0, 1], {0, 2}], 
      Map[Sort, MeshCells[m0, 2], {0, 2}]
    }];
    graph0 = Thread@DirectedEdge[trigI, TriangulationFlips@trigI];
    If[graph0 == {},
      Return@Graph[{trigI}, {}]
    ];
    graph = NestWhile[
      g |-> Union[ Map[Splice@Thread@DirectedEdge[#, TriangulationFlips@#] &,
        Flatten@Select[ConnectedComponents@g, EqualTo[1]@*Length] ], g],
      graph0,
      MemberQ[1]@*Map[Length]@*ConnectedComponents
    ];
    Graph[ UndirectedEdge @@@ DeleteDuplicatesBy[graph, Sort] ]
  ];
SetAttributes[PolytopeTriangulationsGraph, {Protected, ReadProtected}];


SyntaxInformation[PolytopeTriangulations] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulations[td: KeyValuePattern[{}]?ToricDiagramQ] :=
  PolytopeTriangulations[Values@td];
PolytopeTriangulations[pt_?PolytopeQ] :=
  VertexList@PolytopeTriangulationsGraph[pt];
SetAttributes[PolytopeTriangulations, {Protected, ReadProtected}];


SyntaxInformation[pqWebReduced] = {"ArgumentsPattern" -> {_, _.}};
pqWebReduced[pts_?PolytopeQ] :=
  Module[{v, bd, rotateLine, seg},
    {v} = {\[FormalCapitalV]};
    bd = Last@PolytopeVertices[pts];
    rotateLine = NormalizeGCD@*RotationTransform[Pi/2]@*Apply[Subtract];
    seg = Association@MapIndexed[
      v@First@#2 -> #1 &,
      Partition[bd, 2, 1, {1, 1}]
    ];
    {Map[rotateLine, seg], seg}
  ];
SetAttributes[pqWebReduced, {Protected, ReadProtected}];


SyntaxInformation[pqWebFromTriagulation] = {"ArgumentsPattern" -> {_}};
pqWebFromTriagulation[trig_?PolytopeTriangulationQ] :=
  Module[{v, b, coordR, edgeR, edgeFaceC, bdRpMap, bdDivisors, intDivisors},
    {v, b} = {\[FormalCapitalV], \[FormalCapitalB]}; 
    coordR = MapIndexed[First[#2] -> #1 &, Rationalize@MeshCoordinates@trig]; 
    edgeR = MapIndexed[First[#2] -> #1 &, Identity@@@MeshCells[trig,1] ]; 
    edgeFaceC = GroupBy[
      EdgeList@MeshConnectivityGraph[trig, {1, 2}, 1],
      ReplaceAll[coordR]@*ReplaceAll[edgeR]@*Last@*First -> Last@*Last
    ];
    bdRpMap = KeyValueMap[{OrderlessPatternSequence @@ #1} -> b@@#2 &,
      Select[ edgeFaceC, MatchQ[{_}] ]
    ];
    intDivisors = Association@KeyValueMap[
      UndirectedEdge @@ (b/@#2) -> #1 &,
      Reverse@Select[edgeFaceC, MatchQ[{_, _}] ]
    ];
    bdDivisors = Association@MapIndexed[
      DirectedEdge[#1/.bdRpMap, v@@#2] -> #1 &,
      Partition[Reverse@Last@PolytopeVertices@Values@coordR, 2, 1, {1, 1}]
    ];
    Join[intDivisors, bdDivisors]
  ];
SetAttributes[pqWebFromTriagulation, {Protected, ReadProtected}];


pqWebResolvedQ[g_?EdgeListQ] := 
  pqWebResolvedQ[Graph@g];
pqWebResolvedQ[g_?GraphQ] := And @@ MapThread[
  AllTrue[MatchQ@#2]@Pick[VertexDegree@g, VertexList@g, Alternatives @@ #1@EdgeList@g] &,
  {{VertexList@*Cases[_UndirectedEdge], Map[Last]@*Cases[_DirectedEdge]}, {3, 1}}
];
pqWebResolvedQ[g_?pqWebResolvedQ, pos : KeyValuePattern[{}] ] :=
  Module[{rp, vecs},
    rp[v_] := ReplaceAll[{DirectedEdge[_, q_] :> q,
      UndirectedEdge@OrderlessPatternSequence[v, q_] :> q - v}];
    vecs = Map[
      rp[#]@EdgeList@NeighborhoodGraph[g, #] &,
      Pick[VertexList@g, VertexDegree@g, 3]
    ];
    AllTrue[ Map[Total@*Map[NormalizeGCD], vecs/.pos], 
      MatchQ[{0, 0}]
    ]
  ];
SetAttributes[pqWebResolvedQ, {Protected, ReadProtected}];


pqWebFromTriagulationQ[a : KeyValuePattern[_]?(pqWebResolvedQ@*Keys)] :=
  MatchQ[Normal@a, 
    {HoldPattern[Rule][
      _DirectedEdge|_UndirectedEdge, 
      {Repeated[{_Integer, _Integer}, {2}]}
    ] ..}
  ];
pqWebFromTriagulationQ[_] = False;
SetAttributes[pqWebFromTriagulationQ, {Protected, ReadProtected}];


Options[pqWebResolve] = {
  "pqWebLengthCondition" -> None
};
pqWebResolve[pqdata : KeyValuePattern[_], coord : (KeyValuePattern[_] | {} | <||>), opts : OptionsPattern[pqWebResolve] ] :=
  Module[{l, rotLine, intEdges, intVert, bdEdges, partial, coordVec, 
      coordInd, pts, eqs,loopEqs, loopVars, sol0, loopCond, lineCond, loopSol, sol},
    l = \[FormalL];
    rotLine = NormalizeGCD@*RotationTransform[-Pi/2]@*Apply[Subtract];
    intEdges = KeySort@KeySelect[Association@pqdata, MatchQ[_UndirectedEdge] ];
    intVert = Union@VertexList@Keys@intEdges;
    bdEdges = KeySortBy[Last]@KeySelect[Association@pqdata, MatchQ[_DirectedEdge] ];
    {coordVec, coordInd, partial} = ({#1, #2, Union[#1, #2]} &) @@ MapThread[
      Cases[Normal@coord, HoldPattern[Rule][Alternatives@@#1, #2] ] &,
      {{intVert, Map[Indexed[#,1|2] &, intVert]}, {{_Integer, _Integer}, _Integer}}
    ];
    If[ !ContainsExactly[partial, Normal@coord],
      Message[pqWebResolve::coordarg, Complement[Normal@coord, partial], intVert]
    ];
    pts = Map[# -> Lookup[coordVec, #, {Indexed[#, 1], Indexed[#, 2]}/.coordInd] &, intVert];
    eqs = KeyValueMap[(Subtract @@ #1/.pts) == (Identity @@@ l @@ #1) #2 &, rotLine /@ intEdges];
    loopVars = Map[(Identity @@@ l @@ #1) &, Keys@intEdges];
    loopCond = Join[Thread[loopVars > 0], {Element[loopVars, Integers]}];
    sol0 = Solve[eqs];
    If[Length[sol0] == 0 || Simplify[ AnyTrue[loopVars/.Last[sol0,{}], LessEqualThan[0] ], loopCond],
      Message[pqWebResolve::coorderr, partial]; Return[$Failed]
    ];
    loopEqs = Eliminate[eqs, Variables@Values@pts] /. {And->List, True->{}};
    loopCond = Join[Flatten@{loopEqs}, loopCond];
    lineCond = OptionValue[pqWebResolve, opts, "pqWebLengthCondition"] //
      Switch[#,
        _Function, Check[Apply[#, loopVars], True],
        _, True
      ] &;
    If[False === Simplify@Resolve@Join[loopCond, {lineCond}],
      If[MatchQ[partial, {}],
        Message[pqWebResolve::conderr, lineCond],
        Message[pqWebResolve::condcoorderr, lineCond, partial]
      ];,
      loopCond = Simplify@Resolve@Join[loopCond, {lineCond}]
    ];
    loopSol = If[Length@loopEqs == 0, {},
      Last@Minimize[Echo@{Plus @@ loopVars, loopCond}, loopVars, Integers]
    ];
    sol = First@Solve[eqs /. loopSol];
    Join[
      Association[pts /. sol /. {Indexed[_, 1 | 2] -> 0, l[_, _] -> 1}],
      KeyMap[Last, rotLine /@ bdEdges]
    ]
  ];
pqWebResolve[pqdata : KeyValuePattern[_], opts : OptionsPattern[pqWebResolve] ] :=
  pqWebResolve[pqdata, {}, opts];
pqWebResolve[pqdata : KeyValuePattern[_], Automatic, opts : OptionsPattern[pqWebResolve] ] :=
  pqWebResolve[pqdata, {}, opts];
pqWebResolve::coorderr = "Coordinates `1` are not valid for (p,q)-web configuration.";
pqWebResolve::conderr = "Condition `1` is not valid for (p,q)-web configuration. Continuing with no condition.";
pqWebResolve::condcoorderr = "Condition `1` is not valid for (p,q)-web configuration and coordinates `2`. Continuing with no condition.";
pqWebResolve::coordarg = "Coordinates `1` are not integer-valued coordinates of vertices `2`.";
SetAttributes[pqWebResolve, {Protected, ReadProtected}];


pqWebPlotPrim[pq : (_Graph | _?EdgeListQ)] :=
  Module[{intDiv, bdDiv, inG, primF},
    {intDiv, bdDiv} = (Select[EdgeList@pq, MatchQ@#1] &) /@ {_UndirectedEdge, _DirectedEdge};
    inG = Graph[intDiv];
    primF = (If[Length@# == 1, Point@#, Line@#] &);
    Join[
      (Polygon[VertexList@#] &) /@ FindCycle[Graph@inG, Infinity, All],
      (ConicalSimplexHullRegion[
        primF[(FindShortestPath[inG, #1, #2] & @@ Map[First, #1])],
        Map[Last, #1] ] &) /@ Partition[bdDiv, 2, 1, {1, 1}]
    ]
  ];
pqWebPlotPrim[pq_Association] :=
  Module[{rp},
    rp = Normal@Join[
      KeyMap[Last]@KeySelect[pq, MatchQ[_DirectedEdge] ],
      KeyMap[ Apply[Head[#]@*OrderlessPatternSequence, #] &,
        KeySelect[pq, MatchQ[_UndirectedEdge] ]
      ]
    ];
    AssociationMap[
      ReplaceAll[{
        Polygon[l_List] :> 
          First[Intersection @@ (UndirectedEdge @@@ Partition[l,2,1,{1,1}] /. rp)],
        ConicalSimplexHullRegion[(Point | Line)[l_List] | l_List, v_] :>
          First[Intersection @@ (Join[UndirectedEdge @@@ Partition[l, 2, 1], v] /. rp)]
      }],
      pqWebPlotPrim[Graph@Keys@pq]
    ]
  ];


pqWebStyleHandler[{edgePrim_, facePrim_}, opts : OptionsPattern[pqWebPlot] ] :=
  Module[{styled, styO},
    styO = Normal@OptionValue["pqWebStyle"];
    styled = Switch[styO,
      KeyValuePattern[{(Alternatives @@ Keys@Join[edgePrim, facePrim]) -> _}],
      Cases[styO, HoldPattern[Rule][(Alternatives@@Keys@#), _] ] & /@ {edgePrim, facePrim},
      Automatic | None, {{}, {}},
      _, Message[pqWebPlot0::opterr, "pqWebStyle", styO, "directives"]; {{}, {}}
    ];
    {
      Join[
        AssociationThread[ Values@edgePrim, Directive[{}] ],
        Map[Flatten@*Directive]@Association[First@styled /. Normal@edgePrim]
      ],
      Map[Flatten@*Directive]@Association[Last@styled /. Normal@facePrim]
    }
  ];

pqWebLabelHandler[{edgePrim_, facePrim_}, opts : OptionsPattern[pqWebPlot] ] :=
  Module[{labeled, textPos, lblO, sgn},
    sgn[x_] := 1 - 2*UnitStep[-x];
    textPos = Map[ReplaceAll[{
        Polygon[p_] :> ({Mean@p, {0, 0}}),
        ConicalSimplexHullRegion[_[p_], w_] :> ({Mean[p], Normalize@Mean[Normalize /@ w]}),
        Line[p_] :> ({Mean[p], sgn@Cos@VectorAngle[{1,-1}.p, {1, 0}] * Normalize@RotationTransform[-Pi/2][{1, -1}.p]}),
        HalfLine[p_, v_] :> ({p + 1/2 Normalize[v], Normalize@RotationTransform[Pi/2][v]})
      }],
      Join[facePrim, edgePrim]
    ];
    lblO = Normal@OptionValue["pqWebLabel"];
    labeled = Switch[lblO,
      KeyValuePattern[{(Alternatives @@ Keys@textPos) -> _}],
      Cases[lblO, HoldPattern[Rule][(Alternatives @@ Keys@#), _] ] & /@ {edgePrim, facePrim},
      None, {{}, {}},
      _, Message[pqWebPlot::opterr, "pqWebLabel", lblO, "labels"]; {{}, {}}
    ];
    Map[KeyValueMap[{#2, #1} &]@*Association, labeled] /. Normal@textPos
  ];


Options[pqWebPlot] = Normal@Association@{
  Splice@Options[Graphics],
  "pqWebLengthCondition" -> None,
  "pqWebStyle" -> Automatic,
  "pqWebBaseStyle" -> Automatic,
  "pqWebLabel" -> None
};
pqWebPlot[g_?pqWebResolvedQ, coord : KeyValuePattern[_], opts : OptionsPattern[pqWebPlot] ] :=
  Module[{edgePrim, facePrim, sk1, sk2, lbl1, lbl2, gr, bnd, rng},
    edgePrim = AssociationThread[
      EdgeList[g] /. {
        e : UndirectedEdge[i_, f_] :> e | Reverse[e] | pqWebCycle[{i,f}|{f,i}],
        e : DirectedEdge[i_, v_] :> e | v | pqWebCycle[{i}|i, {v}|v]
      },
      EdgeList[g] /. {UndirectedEdge -> Line@*List, DirectedEdge -> HalfLine}
    ];
    facePrim = KeyValueReverse@AssociationMap[
      ReplaceAll[{
        Polygon[{p__}] :> pqWebCycle[{CyclicPatternSequence[p]}],
        ConicalSimplexHullRegion[_[p_], v_] :> pqWebCycle[p | Reverse@p, v | Reverse@v]
      }],
      pqWebPlotPrim[g]
    ];
    {sk1, sk2} = pqWebStyleHandler[{edgePrim, facePrim}, opts];
    {lbl1, lbl2} = pqWebLabelHandler[{edgePrim, facePrim}, opts];
    gr = {
      KeyValueMap[{#2, #1 /. Normal@coord} &, sk1],
      Apply[Text[#1, {1, 0.05} . #2, {0, -1.05} . #2] &, lbl1 /. Normal@coord, {1}], 
      Apply[Text[#1, {1, 0.8} . #2, {0, -0.6} . #2] &, lbl2 /. Normal@coord, {1}]
    };
    bnd[s_] = (PlotRange /. AbsoluteOptions@Graphics[ gr, Sequence@@FilterRules[{opts},Options@Graphics] ]) // 
      Expand@RegionBounds@GeometricTransformation[
        Rectangle @@ Transpose[#], ScalingTransform[{s,s}, Mean/@#] ] &;
    Graphics[gr,
      Sequence @@ FilterRules[FilterRules[{opts}, Options@Graphics], Except[PlotRange|Prolog] ],
      PlotRange -> Switch[PlotRange /. FilterRules[{opts}, PlotRange],
        _?NumericQ | {_?NumericQ,_?NumericQ} | {Repeated[{_?NumericQ,_?NumericQ}, {2}]},
        PlotRange /. FilterRules[{opts}, PlotRange],
        _, bnd@If[Length@lbl2 > 0, 1.4, 1.3]
      ],
      Prolog -> {
        FilterRules[{opts}, Prolog],
        KeyValueMap[{#2, DiscretizeRegion[ #1/.Normal@coord, bnd[2] ]} &, sk2]
      }
    ]
  ];
pqWebPlot[trig_?PolytopeTriangulationQ, coord : (KeyValuePattern[_] | {} | <||>), opts : OptionsPattern[pqWebPlot] ] :=
  pqWebPlot[pqWebFromTriagulation@trig, coord, opts];
pqWebPlot[trig_?PolytopeTriangulationQ, opts : OptionsPattern[pqWebPlot] ] :=
  pqWebPlot[pqWebFromTriagulation@trig, {}, opts];
pqWebPlot[a_?pqWebFromTriagulationQ, coord : (KeyValuePattern[_] | {} | <||>), opts : OptionsPattern[pqWebPlot] ] :=
  Module[{sol},
    sol = pqWebResolve[a, coord, Sequence @@ FilterRules[{opts}, Options@pqWebResolve] ];
    pqWebPlot[Keys@a, sol, opts]
  ];
pqWebPlot[a : (_?pqWebFromTriagulationQ | _?PolytopeTriangulationQ), opts : OptionsPattern[pqWebPlot] ] :=
  pqWebPlot[a, {}, opts];
pqWebPlot::opterr = "The option `1` `2` is not a key-value pattern of pqWebCycle and `3`.";
SetAttributes[pqWebPlot, {Protected, ReadProtected}];


SyntaxInformation[AMaximization] = {"ArgumentsPattern" -> {_, _.}};
AMaximization::arg = "Argument is not a valid potential or toric diagram."
AMaximization[td : KeyValuePattern[{}]?ToricDiagramQ] := MapAt[
    Map[ReplaceAll[#], td] &, 
    AMaximization@Values[td], 
    {2}
  ];
AMaximization[pt_?PolytopeQ] :=
  Module[{trialA, ex, int, bd, pqWex, a, charges, charges0, cc, maxTerm, condTerm, sol},
    {ex, int, bd} = PolytopeVertices[pt];
    charges = Association@MapIndexed[#1 -> a@First@#2 &, ex];
    charges0 = Association[(#1 -> 0 &) /@ Join[int, Complement[bd,ex] ] ];
    pqWex = First /@ PositionIndex[
      RotationTransform[-Pi/2][#2 - #1] & @@@ Partition[ex, 2, 1, {1, 1}]
    ];
    cc = AssociationMap[
      Apply[CyclicRange[#1+1, #2, Length@ex] &]@*ReplaceAll[pqWex], 
      (If[Det@# > 0, #, Reverse@#] &) /@ Subsets[Keys@pqWex, {2}]
    ];
    trialA[c_, m_ : 1] := 9/32*(m (c - 1)^3);
    maxTerm = Expand[
      9/32 * 2 * PolytopeArea[ex] + 
        Total@KeyValueMap[trialA[Total@(a /@ #2), Det@#1] &, cc]
    ];
    condTerm = And[Total[Values@charges] == 2, And @@ Thread[0 < Values@charges <= 1] ];
    sol = Maximize[{maxTerm, condTerm}, Values@charges];
    {RootReduce@First@sol, ReplaceAll[RootReduce@Last@sol] /@ Append[charges, charges0]}
  ];
AMaximization[q_?EdgeListQ, cyc_List] :=
  AMaximization[{q, AssociationThread[VertexList@q, 1]}, cyc];
AMaximization[{q_?EdgeListQ, ranks: KeyValuePattern[_->_Integer]}, cyc_List] :=
  Module[{rk, rkQ, rch, t, h, cond, linSol, trialA, vars, sol},
    rk = Association[ranks];
    rkQ = AssociationMap[Apply[Times]@*Map[rk], q];
    h = GroupBy[q, First -> (rkQ[#] (rch[#] - 1) &), Total];
    t = GroupBy[q, Last -> (rkQ[#] (rch[#] - 1) &), Total];
    cond = Join[
      KeyValueMap[2 rk[#1]^2 + Total[#2] == 0 &]@Merge[{h, t}, Identity],
      (Total[#] == 2 &)@*Map[rch] /@ cyc
    ];
    linSol = First@Solve[cond];
    trialA = 9/32*(Total[rk^2] + Total@Map[rkQ[#]*(rch[#]-1)^3 &, q]/.linSol) // ExpandAll;
    vars = Variables@trialA;
    sol = TimeConstrained[
      RootReduce@Maximize[{trialA, 0 <= vars <= 2}, vars], 
      5, 
      NMaximize[{trialA, 0 <= vars <= 2}, vars]
    ];
    {First@sol, AssociationMap[ 
      ReplaceAll[Union[(linSol/.Last@sol), Last@sol] ]@*rch, q]}
  ];
AMaximization[w_?ToricPotentialQ] :=
  Module[{amax, frch},
    amax = AMaximization[ToricDiagram@w];
    frch = AssociationThread[FieldCases@w, 
      PerfectMatchingMatrix[w].Values[Last@amax] // Simplify // RootReduce 
    ];
    {First@amax, frch}
  ];
(* AMaximization[w_?PotentialQ] :=
  AMaximization[w, AssociationThread[VertexList@Values@QuiverFromFields@w, 1] ];
AMaximization[w_?PotentialQ, ranks: KeyValuePattern[_->_Integer] ] :=
  Module[{fp, q, cyc, sol},
    fp = FieldProducts[w];
    If[AnyTrue[fp, Not@*PossibleMesonQ],
      Message[Mesons::fperr, SelectFirst[Not@*PossibleMesonQ]@fp]; 
      Return[$Failed]
    ];
    q = QuiverFromFields[w];
    cyc = Apply[DirectedEdge, List @@@ fp, {2}];
    sol = AMaximization[{Values@q, ranks}, cyc];
    {First@sol, ReplaceAll[Last@sol] /@ q}
  ]; *)
AMaximization[_] := Null /; Message[AMaximization::arg];
SetAttributes[AMaximization, {Protected, ReadProtected}];


End[]

EndPackage[]
