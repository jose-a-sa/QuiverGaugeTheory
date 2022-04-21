(* ::Package:: *)

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
ZigZagPaths::usage = "";
PolytopePlot::usage = "";
PolytopeArea::usage = "";
PolytopeCentroid::usage = "";
TriangulationFlips::usage = "";
PolytopeTriangulationsGraph::usage = "";
PolytopeTriangulations::usage = "";
pqWeb::usage = "";
pqWebReduced::usage = "";
pqWebQ::usage = "";
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



SyntaxInformation[ToricDiagramQ] = {"ArgumentsPattern" -> {_}};
ToricDiagramQ[td : KeyValuePattern[{}] ] :=
  ToricDiagramQ[Values@Association@td];
ToricDiagramQ[pts_?PolytopeQ] :=
  AllTrue[(Count[pts, #] &) /@ First@PolytopeVertices@pts, #1 === 1 &];
ToricDiagramQ[_] := False;



SyntaxInformation[PolytopeTriangulationQ] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationQ[m_MeshRegion] := And[
  PolytopeQ@Rationalize@MeshCoordinates[m],
  Equal @@ Map[PolytopeArea@*First, MeshCells[m,2] /. MapIndexed[
    First@#2 ->#1 &, Rationalize@MeshCoordinates@m] 
  ]
];
PolytopeTriangulationQ[_] := False;



SyntaxInformation[PolytopeTriangulationCellsQ] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationCellsQ[
  {{Point[_Integer]...}, {Line[{__Integer}]...}, {Polygon[{__Integer}]...}}
] := True;
PolytopeTriangulationCellsQ[_] := False;



SyntaxInformation[PolytopeTriangulationEdgesQ] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulationEdgesQ[{Line[{_,_}]...}] := True;
PolytopeTriangulationEdgesQ[{UndirectedEdge[_,_]...}] := True;
PolytopeTriangulationEdgesQ[{List[_,_]...}] := True;
PolytopeTriangulationEdgesQ[_] := False



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



SyntaxInformation[ReflexivePolytopeQ] = {"ArgumentsPattern" -> {_}};
ReflexivePolytopeQ[pts_?PolytopeQ] := 
  Length[ PolytopeVertices[pts][[2]] ] == 1;
ReflexivePolytopeQ[_] := False;



SyntaxInformation[DualPolytope] = {"ArgumentsPattern" -> {_}};
DualPolytope[pts_?ReflexivePolytopeQ] := 
  Module[{x, c0, p},
    c0 = Round@Mean@PolytopeVertices[pts][[2]];
    p = Array[x, {Length@c0}];
    p /. Solve[And @@ (p.(#1 - c0) >= -1 &) /@ pts, p, Integers]
  ];



SyntaxInformation[NormalizePolytope] = {"ArgumentsPattern" -> {_}};
NormalizePolytope[pt_?PolytopeQ] :=
  Module[{c0, sortV, glMs, newP, polyAngle, min, rules, vert, newP2},
    vert = PolytopeVertices[pt];
    c0 = Round@If[vert[[2]] == {}, PolytopeCentroid[pt], vert[[2]]//Mean ];
    newP = Map[# - c0 &, pt];
    polyAngle[pts_?MatrixQ] := Association[(#2 -> VectorAngle[#1 - #2, #3 - #2] &)
      @@@ Partition[RotateRight@pts, 3, 1, {1, 1}]
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



SyntaxInformation[FastForward] = {"ArgumentsPattern" -> {_}};
FastForward[W_?ToricPotentialQ] :=
  Module[{d, P, nF, nPM, nG, barReduce, QDb, QD, QF, Q, Gt},
    P = PerfectMatchingMatrix[W];
    d = QuiverIncidenceMatrix[W]/.{2->0};
    {nF, nPM} = Dimensions[P];
    nG = First@Dimensions[d];
    QF = NullSpace[P];
    QDb = SolveMatrixLeft[Transpose[P], d];
    barReduce = Transpose@Join[
      {Table[-1, {nG-1}]}, 
      IdentityMatrix[nG-1] 
    ];
    QD = barReduce.QDb;
    Q = Join[QF, QD];
    Gt = NullSpace[Q];
    If[StrictlyCoplanarQ@Transpose@Gt,
      Gt = Join[Most@Gt, {Table[1, {nPM}]}],
      Message[FastForward::notcoplanar]
    ];
    <|"Gt" -> Gt, "QF" -> QF, "QD" -> QD, "QDb" -> QDb|>
  ];
FastForward::notcoplanar = 
  "Resulting polytope is not strictly coplanar.";



SyntaxInformation[ToricDiagram] = {"ArgumentsPattern" -> {_,_.}};
ToricDiagram[W_?ToricPotentialQ, m_?MatrixQ ] :=
  Block[{mat},
    mat = If[Dimensions@m =!= {2,2} || PossibleZeroQ@Det@m, 
      IdentityMatrix[2], m];
    Map[ mat.# &, ToricDiagram[W] ]
  ];
ToricDiagram[W_?ToricPotentialQ] :=
  Module[{ff, pt, ex, int, bd, nex, posEx, posInt, 
      posNEx, exVar, intVar, nexVar, sortedPM},
    ff = FastForward[W];
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



SyntaxInformation[ZigZagPaths] = {"ArgumentsPattern" -> {_}};
ZigZagPaths[W_?ToricPotentialQ] :=
  Module[{td, P, pms, pmGroups, pmDiffs, altPatt, mesZZ},
    td = ToricDiagram[W];
    P = PerfectMatchingMatrix[W];
    pms = AssociationThread[Keys[td], 
      (DeleteCases[FieldCases[W]^#, 1] & /@ Transpose@P)];
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
    GroupBy[
      Normal@Select[AssociationThread[pmDiffs, mesZZ], Length[#] == 1 &],
      First@*Last -> First
    ]
  ];



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
  Module[{trig, tdG, ex, in, bd, coord, optLbl, cellLbl, pattQ, tranfPM},
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
      _, optLbl
    ];
    PolytopePlot[trig,
      "PolytopeCellLabel" -> cellLbl,
      Sequence @@ FilterRules[{opts}, Except["PolytopeCellLabel"] ]
    ]
  ];
PolytopePlot[trig_?PolytopeTriangulationQ, opts : OptionsPattern[PolytopePlot] ] :=
  Module[{remPrim, sortPrim, sortCoord, coord, cell, cellType, cellPts, ptsCells, cellGroups,
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
      (Simplify@RotationTransform[-Pi/2]@Normalize[ Normalize[#3-#2] + Normalize[#2-#1] ] &) 
        @@@ AssociationThread[(List /@ bd), Partition[RotateRight@bd, 3, 1, {1, 1}] ],
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
  Map[(StringJoin["\"", #1, "\""] &), Keys@$polytopeCellLabelFunction], {" ",", ","."}]


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
    If[FailureQ@opt, Message[PolytopePlot::opterr, optV, optN];
      Return[opt] ];
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



SyntaxInformation[PolytopeCentroid] = {"ArgumentsPattern" -> {_}};
PolytopeCentroid[pt_?PolytopeQ] :=
  Module[{xs, ys, as, cx, cy},
    {xs, ys} = Transpose@First@PolytopeVertices[pt];
    as = (xs RotateLeft[ys] - RotateLeft[xs] ys)/2;
    cx = Total[(xs + RotateLeft[xs]) as]/3;
    cy = Total[(ys + RotateLeft[ys]) as]/3;
    {cx, cy}/Abs[Total@as]
  ];



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



SyntaxInformation[PolytopeTriangulations] = {"ArgumentsPattern" -> {_}};
PolytopeTriangulations[td: KeyValuePattern[{}]?ToricDiagramQ] :=
  PolytopeTriangulations[Values@td];
PolytopeTriangulations[pt_?PolytopeQ] :=
  VertexList@PolytopeTriangulationsGraph[pt];



SyntaxInformation[pqWebReduced] = {"ArgumentsPattern" -> {_, _.}};
pqWebReduced[pts_?PolytopeQ] :=
  Module[{V, bd, rotateLine, seg},
    {V} = {\[FormalCapitalV]};
    bd = Last@PolytopeVertices[pts];
    rotateLine = NormalizeGCD@*RotationTransform[Pi/2]@*Apply[Subtract];
    seg = Association@MapIndexed[
      V@First@#2 -> #1 &,
      Partition[bd, 2, 1, {1, 1}]
    ];
    {Map[rotateLine, seg], seg}
  ];



SyntaxInformation[pqWeb] = {"ArgumentsPattern" -> {_}};
pqWeb[trig_?PolytopeTriangulationQ] := 
  Module[{pts, rotateLine, V, B, L, coordRules, edgeRules, faceRules,
      bdVectorAssoc, bdLineAssoc, facePolyAssoc, intPosAssoc, edgeFaceC, 
      intEdges, bdEdges, eqs, sol, basePts, loopEqs, loopVars, loopSol, baseSol},
    {V, B, L} = {\[FormalCapitalV], \[FormalCapitalB], \[FormalL]};
    rotateLine = NormalizeGCD@*RotationTransform[-Pi/2]@*Apply[Subtract];
    pts = Rationalize@MeshCoordinates@trig;
    coordRules = MapIndexed[First@#2->#1 &, pts];
    {edgeRules, faceRules} = Table[
      MapIndexed[First@#2->#1 &, Identity@@@MeshCells[trig, i] ], 
      {i, 1, 2}];
    {bdVectorAssoc, bdLineAssoc} = pqWebReduced[pts];
    facePolyAssoc = GroupBy[
      EdgeList@MeshConnectivityGraph[trig, {2, 0}, 0],
      B@*Last@*First -> ReplaceAll[coordRules]@*Last@*Last
    ];
    edgeFaceC = GroupBy[
      EdgeList@MeshConnectivityGraph[trig, {1, 2}, 1],
      ReplaceAll[coordRules]@*ReplaceAll[edgeRules]@*Last@*First -> Last@*Last
    ];
    intEdges = KeyValueMap[
      UndirectedEdge[B@First@#2, B@Last@#2] -> rotateLine[#1] &,
      Select[edgeFaceC, MatchQ@{_, _}]
    ];
    bdEdges = (DirectedEdge[B@First@#2, #1] -> bdVectorAssoc[#1] &) @@@
      Values@GroupBy[Union[
          KeyValueMap[{#2, #1} &]@Select[edgeFaceC, MatchQ@{_}],
          KeyValueMap[List]@bdLineAssoc
        ],
        Sort@*Last -> First
      ];
    eqs = KeyValueMap[
      (Subtract @@ #1) == #2 (Identity @@@ L @@ #1) &, 
      Association@intEdges
    ];
    basePts = Array[B[#] -> {B[#, 1], B[#, 2]} &, {Length@faceRules}];
    sol = First@Quiet@Solve[eqs /. basePts];
    loopEqs = Select[ sol, MatchQ@HoldPattern[Rule][L[__], _] ];
    loopVars = UniqueCases[ loopEqs, L[__] ];
    loopSol = If[Length@loopEqs > 0, 
      Last@Minimize[
        {Plus@@loopVars, Join[Equal@@@loopEqs, Thread[loopVars>0] ]}, 
        loopVars, Integers], 
      {}];
    baseSol = Select[sol /. loopSol, MatchQ@HoldPattern[Rule][B[__], _] ];
    intPosAssoc = Association[basePts /. baseSol /. {B[_,_]->0, L[_,_]->1}];
    {
      Graph@Keys@Union[intEdges, bdEdges],
      Union[bdVectorAssoc, intPosAssoc],
      Union[bdLineAssoc, facePolyAssoc]
    }
  ];



SyntaxInformation[pqWebQ] = {"ArgumentsPattern" -> {_}};
pqWebQ[expr : {_, _, _}] := 
  MatchQ[expr, {
    _Graph, 
    <|HoldPattern[Rule][(\[FormalCapitalB] | \[FormalCapitalV])[_], _] ..|>, 
    <|HoldPattern[Rule][(\[FormalCapitalB] | \[FormalCapitalV])[_], _] ..|>
  }];
pqWebQ[expr : {_, _}] := 
  MatchQ[expr, {
    <|HoldPattern[Rule][(\[FormalCapitalV])[_], _] ..|>, 
    <|HoldPattern[Rule][(\[FormalCapitalV])[_], _] ..|>
  }];
pqWebQ[expr_] := False;



Options[pqWebPlot] = Normal@Association@{
  Splice@Options[Graphics],
  ImageSize -> Automatic,
  PlotRangePadding -> 2, 
  Frame -> True, 
  FrameTicks -> None
}
SyntaxInformation[pqWebPlot] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};
pqWebPlot[trig_?PolytopeTriangulationQ, opts: OptionsPattern[pqWebPlot] ] :=
  pqWebPlot[ pqWeb[trig], opts ];
pqWebPlot[ pq:{_,_,_}?pqWebQ, opts: OptionsPattern[pqWebPlot] ] :=
  Module[{pqWebGraph, rules, varPoly},
    {pqWebGraph, rules, varPoly} = pq;
    gr = EdgeList@pqWebGraph // ReplaceAll[rules] // ReplaceAll[{
      UndirectedEdge[i_, j_] :> Line[{i,j}],
      DirectedEdge[i_, j_] :> HalfLine[i,j]
    }];
    Graphics[gr, opts,
      PlotRangePadding -> 2, 
      Frame -> True, 
      FrameTicks -> None
    ]
 ];



SyntaxInformation[AMaximization] = {"ArgumentsPattern" -> {_}};
AMaximization::arg = "Argument is not a valid potential or toric diagram."
AMaximization[td : KeyValuePattern[{}]?ToricDiagramQ] := MapAt[
    Map[ReplaceAll[#], td] &, 
    AMaximization@Values[td], 
    {2}
  ];
AMaximization[pt_?PolytopeQ] :=
  Module[{trialA, ex, int, bd, pqWex, a, charges, charges0, CC, maxTerm, condTerm, sol},
    {ex, int, bd} = PolytopeVertices[pt];
    charges = Association@MapIndexed[#1 -> a@First@#2 &, ex];
    charges0 = Association[(#1 -> 0 &) /@ Join[int, Complement[bd,ex] ] ];
    pqWex = First /@ PositionIndex[
      RotationTransform[-Pi/2][#2 - #1] & @@@ Partition[ex, 2, 1, {1, 1}]
    ];
    CC = AssociationMap[
      Apply[CyclicRange[#1+1, #2, Length@ex] &]@*ReplaceAll[pqWex],
      (If[0 < Mod[-Subtract @@ ArcTan @@@ #, 2 Pi] <= Pi, #, Reverse@#] &) 
        /@ Subsets[Keys@pqWex, {2}]
    ];
    trialA[c_, m_:1] := 9/32*m ((c - 1)^3 - (c - 1));
    maxTerm = Total@KeyValueMap[trialA[Total@(a /@ #2), Det@#1] &, CC];
    condTerm = And[ Total[Values@charges] == 2, 0 < Values@charges < 1 ];
    sol = Maximize[{maxTerm, condTerm}, Values@charges];
    {RootReduce@First@sol, ReplaceAll[RootReduce@Last@sol] /@ Append[charges,charges0]}
  ];
AMaximization[W_?PotentialQ] :=
  Module[{fs, fp, r, R, t, h, cond, linSol, trialA, maxF, sol},
    fs = FieldCases[W];
    fp = FieldProducts[W];
    If[AnyTrue[fp, Not@*MesonQ],
      Message[Mesons::fperr, SelectFirst[Not@*MesonQ]@fp]; 
      Return[$Failed]
    ];
    R = Association@MapIndexed[#1 -> r@First@#2 &, fs];
    {h, t} = {GroupBy[fs, First -> R], GroupBy[fs, Last -> R]};
    cond = Join[
      Values@Merge[{h, t}, 
        Apply[Total[#1 - 1] + Total[#2 - 1] + 2 == 0 &]
      ],
      (Total[#] == 2 &)@*Map[R]@*List @@@ fp
    ];
    linSol = First@Solve[cond];
    trialA[c_] := 9/32*((c - 1)^3 - (c - 1));
    maxF = ReplaceAll[linSol]@Total[trialA /@ R];
    sol = TimeConstrained[
      RootReduce@Maximize[{maxF, 0<Variables@maxF<2}, Variables@maxF],
      3,
      NMaximize[{maxF, 0<Variables@maxF<2}, Variables@maxF]
    ];
    {First@sol, RootReduce@*ReplaceAll[Last@sol]@*ReplaceAll[linSol] /@ R}
  ];
AMaximization[_] := Message[AMaximization::arg];



End[]

EndPackage[]
