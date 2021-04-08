(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Polytope`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`",
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Tiling`"
}]


PolytopeQ::usage = "";
ToricDiagramQ::usage = "";
PolytopeVertices::usage = "";
ReflexivePolytopeQ::usage = "";
DualPolytope::usage = "";
NormalizePolytope::usage = "";
FastForward::usage = "";
ToricDiagram::usage = "";
PolytopePlot::usage = "";
PolytopeArea::usage = "";
PolytopeCentroid::usage = "";
pqWeb::usage = "";
pqWebReduced::usage = "";
pqWebQ::usage = "";
pqWebPlot::usage = "";
MixedBoundaryInternalMesh::usage = "";
AMaximization::usage = "";


Begin["`Private`"]


$extremalPMVar = ToExpression["\[FormalP]"];
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
        Total@Map[Function[z, z . z], #], 
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
    d = QuiverIncidenceMatrix[W];
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


SyntaxInformation[ToricDiagram] = {"ArgumentsPattern" -> {_}};
ToricDiagram[W_?ToricPotentialQ] :=
  Module[{ff, pt, ex, int, bd, nex, posEx, posInt, posNEx, vars,
      exVar, intVarPos, intVar, nexVarPos, nexVar, sortedPM},
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
    nexVarPos = Range[
      Min@intVarPos, 
      Min[Min@intVarPos + Length@nex - 1, Length@vars - Length@intVar]
    ] // Join[#, Min@intVarPos - Range[Length@nex - Length@#] ] &;
    nexVar = Extract[ Delete[vars, List /@ intVarPos], List /@ nexVarPos];
    sortedPM = Values@Sort@Flatten@MapThread[
      MapThread[Rule, {#2, Thread@Subscript[#1, Range@Length@#2]}] &,
      {Join[{exVar}, nexVar, intVar], Join[{posEx}, posNEx, posInt]}
    ];
    Association@MapThread[Rule, {sortedPM, pt}]
  ];


Options[PolytopePlot] = {
  ImageSize -> Small,
  PlotRange -> Automatic,
  GridLines -> None,
  GridLinesStyle -> Directive[ AbsoluteThickness[1], GrayLevel[0.75] ],
  "BoundaryStyle" -> Directive[ EdgeForm[{Thick, Black}], FaceForm[Transparent] ],
  "ExtremalStyle" -> Directive[ FaceForm[Black] ],
  "ExtremalPointFunction" -> (Disk[#, 0.15] &),
  "NonExtremalStyle" -> Directive[EdgeForm[{Thick, Black}], FaceForm[Yellow] ],
  "NonExtremalPointFunction" -> (Disk[#, 0.12] &),
  "InternalStyle" -> Directive[ EdgeForm[{Thick, Black}], FaceForm@Lighter[Red, 0.6] ],
  "InternalPointFunction" -> (Disk[#, 0.12] &),
  "PerfectMatchingLabel" -> None,
  "PerfectMatchingLabelStyle" -> Directive[FontSize -> 11],
  "PerfectMatchingLabelFunction" -> (Text[#1, #2 + 0.2 #3, -#3] &),
  "pqWeb" -> None,
  "pqWebStyle" -> Directive[Black],
  "pqWebArrowFunction" -> (Arrow[{Mean[#2], Mean[#2] + Normalize[#1]}, {0.2, -0.2}] &)
};
SyntaxInformation[PolytopePlot] = {
  "ArgumentsPattern" -> {_, OptionsPattern[]},
  "OptionsName" -> {"BoundaryStyle", "ExtremalStyle", "ExtremalPointFunction", 
    "NonExtremalPointFunction", "InternalStyle", "InternalPointFunction", "PerfectMatchingLabel",
    "PerfectMatchingLabelStyle", "PerfectMatchingLabelFunction", "pqWebStyle", "pqWebArrowFunction"}
};
PolytopePlot[td0_?ToricDiagramQ, opts : OptionsPattern[{PolytopePlot, Graphics}] ] :=
  Module[{getOpt, td, ex, int, bd, bdLines, grPts, pqWGr, pmText, bounds, gr},
    getOpt[o_] := OptionValue[o] // If[MatchQ[#, Automatic],
      OptionValue[PolytopePlot, Options@PolytopePlot, o], #] &;
    td = PositionIndex@Switch[td0,
      KeyValuePattern[{}], Association@td0,
      _?PolytopeQ, td0
    ];
    {ex, int, bd} = PolytopeVertices[Keys@td];
    bdLines = {getOpt["BoundaryStyle"], Polygon@ex};
    grPts = MapThread[{getOpt[#2], getOpt[#3] /@ #1} &,
      {{ex, Complement[bd, ex], int},
      {"ExtremalStyle", "NonExtremalStyle", "InternalStyle"},
      {"ExtremalPointFunction", "NonExtremalPointFunction", "InternalPointFunction"}}
    ];
    pmText = polytopePlotPMLabel[(KeyTake[td, #] &) /@ {ex, int, bd}, opts];
    pqWGr = polytopePlotpqWeb[Keys@td, opts];
    gr = {bdLines, grPts, pqWGr, pmText};
    bounds = polytopePlotBounds[gr, opts];
    Graphics[gr,
      Sequence @@ FilterRules[{opts}, Except@Options@PolytopePlot],
      GridLines -> (Range @@@ bounds),
      GridLinesStyle -> getOpt["GridLinesStyle"],
      PlotRange -> If[bounds === None, OptionValue["PlotRange"], bounds],
      ImageSize -> OptionValue["ImageSize"]
    ]
  ];
PolytopePlot::ptsform = "The first arguments";
PolytopePlot[_, OptionsPattern[] ] := Message[PolytopePlot::ptsform];


polytopePlotPMLabel[{ex_, int_, bd_}, opts : OptionsPattern[{PolytopePlot, Graphics}] ] :=
  Module[{td, getOpt, lbl, normalsBd, normalInt, dirs, textF, textS},
    getOpt[o_] := OptionValue[o] // If[MatchQ[#, Automatic],
      OptionValue[PolytopePlot, Options@PolytopePlot, o], #] &;
    td = Union[bd, int];
    lbl = OptionValue["PerfectMatchingLabel"] // Switch[#,
      Automatic | "Count", DeleteCases[Length /@ td, 1],
      All | "CountAll", Length /@ td,
      "LastVariable" | "Last", Last /@ td,
      "Variable", Replace[Subscript[x:Except[ \[FormalP] ],_] :> x]@*Last /@ td,
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
    normalInt = ReIm@Exp[I(Round[Arg[{1, I}.PolytopeCentroid@Keys@ex]+Pi/4, Pi/2]-Pi/4)];
    dirs = Association@Join[
      Thread[Keys@bd -> normalsBd],
      Map[# -> normalInt &, Keys@int]
    ];
    textF = getOpt["PerfectMatchingLabelFunction"];
    textS = getOpt["PerfectMatchingLabelStyle"];
    KeyValueMap[textF[Style[#2, textS], #1, dirs@#1] &, lbl]
  ];


polytopePlotpqWeb[pt_, opts : OptionsPattern[{PolytopePlot, Graphics}] ] :=
  Module[{getOpt, remV, remNeg, pqVec, pqAssoc, n, pqW, defStyle, 
      style, arrowF, arrowG, defS},
    getOpt[o_] := OptionValue[o] // If[MatchQ[#, Automatic],
      OptionValue[PolytopePlot, Options@PolytopePlot, o], #] &;
    remV = ReplaceAll[\[FormalCapitalV] -> Identity];
    {pqVec, pqAssoc} = KeyMap[remV] /@ pqWebReduced[pt];
    n = Length@pqVec;
    remNeg = ReplaceAll[i_?Negative :> i + n + 1];
    pqW = remV@OptionValue["pqWeb"] // Switch[#,
      Automatic | All | True, Range[n],
      _List, Union[remNeg@#],
      _, {}] & // Select@MatchQ[i_Integer /; 1 <= i <= n];
    defStyle = OptionValue[PolytopePlot, Options@PolytopePlot, "pqWebStyle"];
    style = getOpt["pqWebStyle"] // Switch[#,
      KeyValuePattern[{}],
      KeyMap[remNeg]@Association@#,
      {(_Directive | {__}) ..}, 
      AssociationThread[Range@Length@#, Apply[Directive]@*Normal /@ #],
      _, AssociationThread[Range@n, Directive@#]
    ] & // KeySelect@MatchQ[i_Integer /; 1 <= i <= n];
    arrowF = getOpt["pqWebArrowFunction"];
    arrowG = Merge[{pqVec, pqAssoc}, Apply@arrowF];
    {defStyle, Values@Merge[KeyTake[pqW] /@ {arrowG, style}, Reverse]}
  ];


polytopePlotBounds[gr_, opts : OptionsPattern[{PolytopePlot, Graphics}] ] :=
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


SyntaxInformation[pqWeb] = {"ArgumentsPattern" -> {_, _.}};
pqWeb[pts_?PolytopeQ, meshF_ : DelaunayMesh] := 
  Module[{rotateLine, V, B, L, trig, coordRules, edgeRules, faceRules,
      bdVectorAssoc, bdLineAssoc, facePolyAssoc, intPosAssoc, edgeFaceC, 
      intEdges, bdEdges, eqs, sol, basePts, loopEqs, loopVars, loopSol, baseSol},
    rotateLine = NormalizeGCD@*RotationTransform[-Pi/2]@*Apply[Subtract];
    {V, B, L} = {\[FormalCapitalV], \[FormalCapitalB], \[FormalL]};
    trig = meshF[pts];
    coordRules = MapIndexed[First@#2->#1 &, Rationalize@MeshCoordinates@trig];
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


SyntaxInformation[pqWebPlot] = {"ArgumentsPattern" -> {_, _.}};
pqWebPlot[pts_?PolytopeQ, meshF_ : DelaunayMesh] :=
  pqWebPlot[ pqWeb[pts, meshF], meshF];
pqWebPlot[pq:{_,_,_}?pqWebQ, meshF_ : DelaunayMesh] :=
  Module[{pqWebGraph, rules, varPoly},
    {pqWebGraph, rules, varPoly} = pq;
    gr = EdgeList@pqWebGraph // ReplaceAll[rules] // 
      ReplaceAll[ UndirectedEdge[i_, j_] :> Line[{i,j}] ] //
      ReplaceAll[ DirectedEdge[i_, j_] :> HalfLine[i,j] ];
    Graphics[gr, PlotRangePadding -> 2, Frame -> True, FrameTicks -> None]
 ];


SyntaxInformation[MixedBoundaryInternalMesh] = {"ArgumentsPattern" -> {_, _.}};
MixedBoundaryInternalMesh[pts_?PolytopeQ, internalMeshF_ : DelaunayMesh] := 
  Module[{emptyIntersectionQ, triangleLinesQ, ex, bd, int, 
      intLines0, intLines, cells0, cells1, cells2, sbset1},
    {ex, int, bd} = PolytopeVertices[pts];
    emptyIntersectionQ[x__] := MatchQ[
      RegionIntersection[x],
      Point[{(Alternatives @@ pts) ..}] | EmptyRegion[_]
    ];
    triangleLinesQ[l_] := MatchQ[
      {{y_, x_} | {x_, y_}, {z_, x_} | {x_, z_}} /; 
        (FreeQ[l, x] && ContainsExactly[{z, y}, l])
    ];
    If[Length@int == 0, Return[internalMeshF@pts] ];
    intLines0 = Switch[Length@int,
      1, {},
      2, {int},
      _, Identity @@@ MeshCells[internalMeshF@int, 1] /. 
      Thread[Range@Length@int -> int]
    ];
    intLines = Fold[
      If[#1 == {} || emptyIntersectionQ[Line@#1,Line@#2], Append[#1,#2], #1] &,
      intLines0, 
      SortBy[ Tuples[{int, bd}], Norm@*Apply[Subtract] ]
    ];
    cells0 = Point /@ pts;
    cells1 = Line /@ Join[intLines, Partition[bd, 2, 1, {1, 1}] ];
    sbset1 = Subsets[Identity @@@ cells1, {2}];
    cells2 = MinimalBy[Union @@ Table[
        Polygon@*Union @@@ Select[sbset1, triangleLinesQ@l],
        {l, Identity @@@ cells1}
      ], Area];
    MeshRegion[pts, {cells0,cells1,cells2}/.Thread[pts -> Range@Length@pts] ]
  ];


SyntaxInformation[AMaximization] = {"ArgumentsPattern" -> {_}};
AMaximization::arg = "Argument is not a valid potential or toric diagram."
AMaximization[td : KeyValuePattern[{}]?ToricDiagramQ] :=
  MapAt[
    KeyMap[ Last@*ReplaceAll[PositionIndex@Association@td] ], 
    AMaximization[Values@td], 
    {2}
  ];
AMaximization[pt_?PolytopeQ] :=
  Module[{trialA, ex, int, bd, pqWex, a, charges, CC, maxTerm, condTerm, sol},
    {ex, int, bd} = PolytopeVertices[pt];
    charges = Association@MapIndexed[#1 -> a@First@#2 &, ex];
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
    {RootReduce@First@sol, ReplaceAll[RootReduce@Last@sol] /@ charges}
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


End[]

EndPackage[]
