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
PolytopePlot::usage = "";
PolytopeArea::usage = "";
PolytopeCentroid::usage = "";
PolytopeTriangulationsGraph::usage = "";
PolytopeTriangulations::usage = "";
pqWeb::usage = "";
pqWebReduced::usage = "";
pqWebQ::usage = "";
pqWebPlot::usage = "";
MixedBoundaryInternalMesh::usage = "";
AMaximization::usage = "";
SubQuiverRepresentations::usage = "";
KahlerChambers::usage = "";
KahlerChambersCompatibility::usage = "";
KahlerChambersFlowGraph::usage = "";
(* ResolutionsFlowGraph::usage = ""; *)


Begin["`Private`"]


$extremalPMVar = ToExpression["\[FormalP]"];
$FIvar = ToExpression["\[FormalXi]"];
$perfectMatchingVars = ToExpression@Delete[
  CharacterRange["\[FormalA]", "\[FormalZ]"], 
  {{1}, {5}, {9}, {15}, {21}}
] // DeleteCases[$extremalPMVar];
$pmVars = Alternatives @@ Join[{$extremalPMVar}, $perfectMatchingVars];


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
  Module[{c0, sortV, glMs, newP, polyAngle, min, rules, vert},
    vert = PolytopeVertices[pt];
    c0 = Round@If[vert[[2]] == {}, PolytopeCentroid[pt], vert[[2]]//Mean ];
    newP = Map[# - c0 &, pt];
    polyAngle[pts_?MatrixQ] := (VectorAngle[#1 - #2, #3 - #2] &) @@@ 
      Partition[RotateRight@pts, 3, 1, {1, 1}];
    sortV = Block[{ex, int, bd, ang},
      {ex, int, bd} = PolytopeVertices[#];
      ang = polyAngle[ex];
      {
        Total[EuclideanDistance @@@ Partition[ex, 2, 1, {1, 1}] ], 
        Abs@Apply[Subtract]@MinMax@ang,
        Total@Map[z |-> z.z, #], 
        -Values@KeySort@CountsBy[bd, First], 
        -Values@KeySort@CountsBy[bd, Last]
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
    newP /. First@Keys@KeySortBy[rules, Length]
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
    <|"Gt" -> Gt, "QF" -> QF, "QD" -> QD|>
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
  Module[{ff, pt, ex, int, bd, nex, posEx, posInt, posNEx, vars, mat,
      exVar, intVarPos, intVar, nextStart, nexVarPos, nexVar, sortedPM},
    ff = FastForward[W];
    pt = NormalizePolytope@Transpose@Most@First@ff;
    {ex, int, bd} = PolytopeVertices[pt];
    nex = Complement[bd, ex];
    {posEx, posInt, posNEx} = {
      FirstPosition[pt, #] & /@ ex,
      Position[pt, #] & /@ int,
      Position[pt, #] & /@ nex};
    exVar = $extremalPMVar;
    vars = $perfectMatchingVars;
    intVarPos = Riffle[ Range@Ceiling[Length@int/2] - 1, -Range@Floor[Length@int/2] ] + 
      Position[vars, \[FormalS] ][[1, 1]];
    intVar = Extract[vars, List /@ intVarPos];
    nextStart = If[Length@int > 0, Min@intVarPos, Position[vars, \[FormalS] ][[1, 1]] + 1];
    nexVarPos = Range[
      nextStart, 
      Min[nextStart + Length@nex - 1, Length@vars - Length@intVar]
    ] // Join[#, nextStart - Range[Length@nex - Length@#] ] &;
    nexVar = Extract[ Delete[vars, List /@ intVarPos], List /@ nexVarPos];
    sortedPM = Values@Sort@Flatten@MapThread[
      MapThread[Rule, {#2, Thread@Subscript[#1, Range@Length@#2]}] &,
      {Join[{exVar}, nexVar, intVar], Join[{posEx}, posNEx, posInt]}
    ];
    AssociationThread[sortedPM, pt]
  ];


Options[PolytopePlot] = Normal@Association@{
  Splice@Options[Graphics],
  ImageSize -> Small,
  PlotRange -> Automatic,
  GridLines -> None,
  PlotRangePadding -> Scaled[0.1],
  GridLinesStyle -> Directive[ AbsoluteThickness[1], GrayLevel[0.75] ],
  "BoundaryStyle" -> Directive[ EdgeForm[{Thick, Black}], FaceForm[Transparent] ],
  "TriangulationStyle" -> Directive[{Black, Thickness[0.012]}],
  "ExtremalStyle" -> Directive[ FaceForm[Black] ],
  "ExtremalPointFunction" -> (Disk[#, 0.15] &),
  "NonExtremalStyle" -> Directive[EdgeForm[{Thick, Black}], FaceForm[Yellow] ],
  "NonExtremalPointFunction" -> (Disk[#, 0.12] &),
  "InternalStyle" -> Directive[ EdgeForm[{Thick, Black}], FaceForm@Lighter[Red, 0.6] ],
  "InternalPointFunction" -> (Disk[#, 0.12] &),
  "Labels" -> None,
  "LabelsStyle" -> Directive[Background -> Directive[Opacity[3/4], White], FontSize -> 12],
  "LabelsFunction" -> (Text[#1, #2 + 0.2 #3, -#3] &),
  "pqWeb" -> None,
  "pqWebStyle" -> Directive[Black, Thick, Arrowheads[0.085] ],
  "pqWebArrowFunction" -> (Arrow[{Mean[#2], Mean[#2] + Normalize[#1]}, {0.2, -0.2}] &)
};
PolytopePlot[td0_?ToricDiagramQ, opts : OptionsPattern[PolytopePlot] ] :=
  PolytopePlot[td0, None, opts];
PolytopePlot[trig_?PolytopeTriangulationQ, opts : OptionsPattern[PolytopePlot] ] :=
  PolytopePlot[Rationalize@MeshCoordinates@trig, MeshCells[trig, All], opts];
PolytopePlot[
    td0_?ToricDiagramQ, 
    triangCells: (_?PolytopeTriangulationEdgesQ) | (_?PolytopeTriangulationCellsQ) | None | {}, 
    opts : OptionsPattern[PolytopePlot] ] :=
  Module[{getOpt, tdGrouped, ex, int, bd, bdLines, trigLines, grPts, pqWGr, pmText, bounds, gr},
    getOpt[o_] := OptionValue[o] // If[MatchQ[#, Automatic],
      OptionValue[PolytopePlot, Options@PolytopePlot, o], #] &;
    {meshPts, tdGrouped} = Switch[td0,
      KeyValuePattern[{}], {Values@td0, PositionIndex@Association@td0},
      _?PolytopeQ, {td0, PositionIndex@td0}
    ];
    {ex, int, bd} = PolytopeVertices[Keys@tdGrouped];
    bdLines = {getOpt["BoundaryStyle"], Polygon@ex};
    trigLines = {getOpt["TriangulationStyle"], Switch[triangCells,
        _?PolytopeTriangulationCellsQ, 
        triangCells[[2]] /. MapIndexed[First@#2 -> #1 &, meshPts],
        {Line[{__Integer}]...}, 
        triangCells /. MapIndexed[First@#2 -> #1 &, meshPts],
        _?PolytopeTriangulationEdgesQ, Line @@@ triangCells,
        _, {}
      ]
    };
    grPts = MapThread[{getOpt[#2], getOpt[#3] /@ #1} &,
      {{ex, Complement[bd, ex], int},
      {"ExtremalStyle", "NonExtremalStyle", "InternalStyle"},
      {"ExtremalPointFunction", "NonExtremalPointFunction", "InternalPointFunction"}}
    ];
    pmText = polytopePlotPMLabel[(KeyTake[tdGrouped, #] &) /@ {ex, int, bd}, opts];
    pqWGr = polytopePlotpqWeb[Keys@tdGrouped, opts];
    gr = {pqWGr, trigLines, bdLines, grPts, pmText};
    bounds = polytopePlotBounds[gr, opts];
    Graphics[gr,
      Sequence @@ FilterRules[{opts}, Except[{
        GridLines,GridLinesStyle,PlotRange,PlotRangePadding,ImageSize,"Labels"},
        Options@Graphics]
      ],
      GridLines -> (Range @@@ bounds),
      GridLinesStyle -> getOpt["GridLinesStyle"],
      PlotRange -> If[bounds === None, OptionValue["PlotRange"], bounds],
      PlotRangePadding -> If[bounds === None, OptionValue["PlotRangePadding"], None],
      ImageSize -> OptionValue["ImageSize"]
    ]
  ];
PolytopePlot::ptsform = "The first arguments";
PolytopePlot[_, OptionsPattern[] ] := Message[PolytopePlot::ptsform];


polytopePlotPMLabel[{ex_, int_, bd_}, opts : OptionsPattern[PolytopePlot] ] :=
  Module[{td, getOpt, lbl, normalsBd, normalInt, dirs, textF, textS},
    getOpt[o_] := OptionValue[o] // If[MatchQ[#, Automatic],
      OptionValue[PolytopePlot, Options@PolytopePlot, o], #] &;
    td = Union[bd, int];
    lbl = OptionValue["Labels"] // Switch[#,
      Automatic | "Count", DeleteCases[Length /@ td, 1],
      All | "CountAll", Length /@ td,
      "LastVariable" | "Last", Last /@ td,
      "Variable", Replace[Subscript[x:Except[$extremalPMVar],_] :> x]@*Last /@ td,
      KeyValuePattern[{}],
      Union[
        KeyMap[ Keys[td][[#]]& ]@KeySelect[ Association@#,
          MatchQ[i_Integer /; 1<=Abs[i]<=Length@td] ],
        KeyTake[Association@#, Keys@td]
      ],
      _, Association[]
    ] &;
    normalsBd = RotationTransform[-Pi/2]@Normalize[ Normalize[#3-#2]+Normalize[#2-#1] ] & 
      @@@ Partition[RotateRight@Keys@bd, 3, 1, {1, 1}];
    (* normalInt = ReIm@Exp[I(Round[Arg[{1, I}.PolytopeCentroid@Keys@ex]+Pi/4, Pi/2]-Pi/4)]; *)
    normalInt = Normalize@*RotationTransform[-Pi/2]@*Subtract @@  
      First@First@MinimalBy[N@*Last]@Flatten@Outer[#2 -> RegionDistance[Line@#2, #1] &, 
        Keys@int, Partition[Keys@ex, 2, 1, {1, 1}], 1];
    dirs = Association@Join[
      Thread[Keys@bd -> normalsBd],
      Map[# -> normalInt &, Keys@int]
    ];
    textF = getOpt["LabelsFunction"];
    textS = getOpt["LabelsStyle"];
    KeyValueMap[textF[Style[#2, textS], #1, dirs@#1] &, lbl]
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
    minBounds = {Floor[#1], Ceiling[#2]} & 
      @@@ RegionBounds@RegionUnion@Cases[gr, _?RegionQ, Infinity];
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
  Module[{pts, edges, faces, fcPairs, fcPairsEdge, fcPairsEdgeNew,
      facesFlipR, edgesFlitR, facesTree, edgesTree},
    pts = MapIndexed[First@#2 -> #1 &, Rationalize@MeshCoordinates@trig];
    edges = Map[Sort, MeshCells[trig, 1], {0, 2}];
    faces = MeshCells[trig, 2];
    fcPairs = Select[
      List @@@ Map[Last, EdgeList@MeshConnectivityGraph[trig, 2], {2}],
      Length@MeshCoordinates@ConvexHullMesh[ 
        Union @@ First /@ (faces[[#]]/.pts) 
      ] == 4 &
    ];
    fcPairsEdge = KeyMap[faces[[#]] &]@AssociationMap[
      Line[ Intersection @@ Map[First, faces[[#1]], {1}] ] &,
      fcPairs
    ];
    fcPairsEdgeNew = Association@KeyValueMap[
      {fcs, e} |-> (Map[Polygon@*Sort@*Apply[Join], 
        Thread[{List /@ First@e, #}, List, 1] ] -> Line@Sort[#] &)@
        Flatten@Map[DeleteCases[Alternatives@@First@e]@*First, fcs],
      fcPairsEdge
    ];
    facesFlipR = AssociationThread[Keys@fcPairsEdge, Keys@fcPairsEdgeNew];
    edgesFlitR = AssociationThread[Values@fcPairsEdge, Values@fcPairsEdgeNew];
    facesTree = Map[Sort, Union[DeleteCases[faces, Alternatives @@ #1], #2], 
      {0, 2}] & @@@ Normal@facesFlipR;
    edgesTree = Map[Sort, Union[DeleteCases[edges, #1], {#2}], 
      {0, 2}] & @@@ Normal@edgesFlitR;
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
      g |-> Union[Join @@ (Thread@DirectedEdge[#, TriangulationFlips@#] & /@
        Flatten@Select[ConnectedComponents@g, EqualTo[1]@*Length]), g],
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
    fs = Fields[W];
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


SyntaxInformation[SubQuiverRepresentations] = {"ArgumentsPattern" -> {_,_.}};
SubQuiverRepresentations[W_?ToricPotentialQ] := 
  SubQuiverRepresentations[W, Automatic];
SubQuiverRepresentations[W_?ToricPotentialQ, pmPairs : {__} | Automatic] :=
  Module[{td, P, pm, Q, properRep, F, allReps, pairs},
    Q = QuiverFromFields@W;
    td = ToricDiagram[W];
    F = Sort@VertexList[Values@Q];
    P = PerfectMatchingMatrix[W];
    pm = AssociationThread[Keys@td, DeleteCases[Keys[Q]^#, 1] & /@ Transpose@P];
    allReps = Subsets[F, {1, Length[F] - 1}];
    properRep = g |-> Select[allReps, 
      ContainsExactly[VertexOutComponent[g, #], #] &];
    pairs = If[MatchQ[pmPairs, Automatic], List /@ Keys@td, List @@@ pmPairs];
    AssociationMap[
      properRep@Values@KeyDrop[ Q, Flatten[# /. pm] ] &, 
      pairs
    ]
  ];



SimplifyThetaCondition = Module[{vars, rule},
  vars = Sort@UniqueCases[#, $FIvar[_] ];
  rule = Last@vars -> -Total@Most@vars;
  ReplaceAll[rule]@#
] &;
ToNonStrict = ReplaceAll[{Greater -> GreaterEqual, Less -> LessEqual}];
ToStrict = ReplaceAll[{GreaterEqual -> Greater, LessEqual -> Less}];

SyntaxInformation[KahlerChambers] = {"ArgumentsPattern" -> {_}};
KahlerChambers[W_?ToricPotentialQ] :=
  KahlerChambers[ToricDiagram@W];
KahlerChambers[td: KeyValuePattern[{}]?ToricDiagramQ] :=
  Module[{tdG},
    tdG = SortBy[{Length@#, #} &]@PositionIndex[td];
    AssociationThread[Keys@tdG, #] & /@ Tuples[Values@tdG]
  ];



Options[KahlerChambersCompatibility] := DeleteDuplicatesBy[First]@{
  "ShowProgress" -> False
};
SyntaxInformation[KahlerChambersCompatibility] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]}
};
KahlerChambersCompatibility[W_?ToricPotentialQ, 
    opts: OptionsPattern[KahlerChambersCompatibility] ] :=
  Module[{k, status, indicator, td, triang, triangEdgesF, 
      KC, F, stabilityC, tbPairs, pairsR, properPairs, tb},
    F = VertexList[Values@QuiverFromFields@W];
    td = ToricDiagram[W];
    triang = PolytopeTriangulations[Values@td];
    triangEdgesF = (Identity @@@ MeshCells[#, 1] /. MapIndexed[
      First@#2 -> #1 &, Rationalize@MeshCoordinates@#] &);
    KC = KahlerChambers[td];
    stabilityC = Apply[And[##, Total@Map[$FIvar, F] == 0] &]@*Map[
      LessThan[0]@*Total@*Map[$FIvar] ];
    tbPairs = Outer[Join[(#1 /. #2), 
      List /@ DeleteCases[ Subscript[$extremalPMVar,_] ]@Values@#2] &,
      Map[triangEdgesF, triang], KC, 1];
    properPairs = DeleteDuplicatesBy[Sort]@Flatten[tbPairs, 2];
    {k, lenK, status} = {0, Length@properPairs,
      "Simplifying theta-stability from sub-quiver representations..."};
    If[OptionValue["ShowProgress"] === True, 
      Echo@Labeled[
        ProgressIndicator[Dynamic[k], {0, Dynamic[lenK]}, 
          BaselinePosition->Scaled[0.1] ],
        Style[Dynamic[status], FontFamily -> Automatic], 
        Right
      ]
    ];
    pairsR = Map[
      Block[{},
        k++;
        Simplify@stabilityC[#]
      ] &, 
      SubQuiverRepresentations[W, properPairs]
    ];
    {k, lenK, status} = {0, Times @@ (Dimensions[tbPairs][[{1,2}]]),
      "Simplifying compatibility table entries..."};
    tb = Map[
      Block[{},
        k++;
        FullSimplify@Apply[And, #]
      ] &,
      tbPairs /. Normal@KeyMap[#1 | Reverse@#1 &]@pairsR, 
      {2}
    ];
    status = "Done!";
    AssociationThread[triang, (AssociationThread[KC, #] &) /@ tb]
  ];



kcTablePattQ = MatchQ[
  KeyValuePattern[_MeshRegion -> KeyValuePattern[
    KeyValuePattern[{{__?NumericQ} -> Subscript[$pmVars, _]}] -> _]
  ]
];
Options[KahlerChambersFlowGraph] := DeleteDuplicatesBy[First]@{
  "RegionTests" -> Automatic,
  "ShowProgress" -> False
};
SyntaxInformation[KahlerChambersFlowGraph] = {
  "ArgumentsPattern" -> {_, _, OptionsPattern[]},
  "OptionsName" -> {"RegionTests"}
};
KahlerChambersFlowGraph[WI_?ToricPotentialQ, WF_?ToricPotentialQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] :=
  KahlerChambersFlowGraph[
    KahlerChambersCompatibility[WI, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    KahlerChambersCompatibility[WF, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    opts];
KahlerChambersFlowGraph[WI_?ToricPotentialQ, tbF_?kcTablePattQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] :=
  KahlerChambersFlowGraph[
    KahlerChambersCompatibility[WI, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    tbF, 
    opts];
KahlerChambersFlowGraph[tbI_?kcTablePattQ, WF_?ToricPotentialQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] :=
  KahlerChambersFlowGraph[
    tbI,
    KahlerChambersCompatibility[WF, "ShowProgress" -> OptionValue["ShowProgress"] ], 
    opts];
KahlerChambersFlowGraph[tbI_?kcTablePattQ, tbF_?kcTablePattQ,
    opts : OptionsPattern[KahlerChambersFlowGraph] ] := 
  Module[{k = 0, oskcI, oskcF, trigI, trigF, meshToGr, kcRulesFunc,
      kcRulesI, kcRulesF, vars, testRules, graph, indicator, status},
    {trigI, trigF} = Keys /@ {tbI, tbF};
    {oskcI, oskcF} = Keys /@ {First@tbI, First@tbF};
    kcRulesFunc = {tb, oskc, trig} |-> DeleteCases[False]@Association[
      Join @@ MapThread[Rule, {Outer[List, trig, oskc, 1],
          ToNonStrict@Simplify@SimplifyThetaCondition@Map[Values, tb, {0, 1}]
        }, 2]
    ];
    {status, indicator} = {"Simplifying theta-stability conditions...",
      ProgressIndicator[Appearance -> "Indeterminate", BaselinePosition -> Scaled[0.1] ]};
    If[OptionValue["ShowProgress"] === True, 
      Echo@Dynamic[Labeled[Dynamic[indicator],
        Style[Dynamic[status], FontFamily -> Automatic], Right]
      ]
    ];
    {kcRulesI, kcRulesF} = kcRulesFunc @@@ {
      {tbI, oskcI, trigI}, {tbF, oskcF, trigF}};
    vars = Sort@UniqueCases[Values /@ {kcRulesI, kcRulesF}, $FIvar[_] ];
    testRules = Switch[OptionValue["RegionTests"],
      KeyValuePattern[{}], Normal@OptionValue["RegionTests"],
      _, {
        (RegionWithin[#2, #1] &) -> DirectedEdge,
        (RegionWithin) -> (DirectedEdge[#2, #1] &)
      }
    ];
    {status, indicator} = {"Comparing chambers from both models...",
      ProgressIndicator[Dynamic[k], {0, Length[kcRulesI]*Length[kcRulesF]}, 
        BaselinePosition -> Scaled[0.1] ]};
    graph = Join @@ Outer[
      Block[{}, 
        k++;
        Splice@Apply[
          {f1, f2} |-> If[f1 @@ Map[Last, {##}], f2 @@ Map[First, {##}], Nothing], 
          testRules, {1}]
      ] &,
      Normal[ImplicitRegion[#, Evaluate@vars] & /@ kcRulesI],
      Normal[ImplicitRegion[#, Evaluate@vars] & /@ kcRulesF],
      1
    ];
    status = "Done!";
    Graph[graph]
  ];



End[]

EndPackage[]
