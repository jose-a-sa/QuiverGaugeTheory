Unprotect["QuiverGaugeTheory`Tiling`*"];
ClearAll["QuiverGaugeTheory`Tiling`*"];


BeginPackage["QuiverGaugeTheory`Tiling`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Polytope`"
}]


ToricPotentialNodes::usage = "";
PerfectMatchingMatrix::usage = "";
PerfectMatchings::usage = "";
KasteleynMatrix::usage = "";
BraneTiling::usage = "";
BraneTilingGraph::usage = "";
TwistedZigZag::usage = "";
IntegrateOutTiling::usage = "";
ZigZagDeformation::usage = "";
ZigDeformation::usage = "";
ZagDeformation::usage = "";
ContractDigons::usage = "";



Begin["`Private`"]


$grRng = 2;
$a = \[FormalA];
$x = \[FormalX];
$y = \[FormalY];
$nW = \[FormalW];
$nB = \[FormalB];


ToricPotentialNodes[w_?ToricPotentialQ] :=
  Module[{fp, res},
    fp = FieldProducts[w];
    res = Join @@ KeyValueMap[{k, v} |-> MapIndexed[#1 -> k @@ #2 &, v],
      GroupBy[fp, Lookup[<|-1 -> $nB, 1 -> $nW|>, Coefficient[w, #] ] &]
    ];
    Association[res][[ Key /@ fp ]]
  ];
SetAttributes[ToricPotentialNodes, {Protected, ReadProtected}];


SyntaxInformation[PerfectMatchingMatrix] = {"ArgumentsPattern" -> {_}};
PerfectMatchingMatrix[w_?ToricPotentialQ] :=
  Module[{k, fs, pmList, a = $a},
    fs = FieldCases[w];
    k = SparseArray@KasteleynMatrix[w, {1, 1}];
    pmList = ReplaceAll[a -> Identity]@MonomialList[
      ReplaceAll[HoldPattern[Times][-1, x_] :> x]@Expand@Det[k], a/@FieldCases@w];
    If[Dimensions[k] == {1,1}, pmList = List /@ pmList];
    Boole@Outer[
      MemberQ[#2, #1] &, fs, (Alternatives @@@ pmList), 1
    ]
  ];
SetAttributes[PerfectMatchingMatrix, {Protected, ReadProtected}];


SyntaxInformation[PerfectMatchings] = {"ArgumentsPattern" -> {_}};
PerfectMatchings[w_?ToricPotentialQ] :=
  Module[{fs, pmV, pmm},
    fs = FieldCases[w];
    pmV = Keys@ToricDiagram[w];
    pmm = PerfectMatchingMatrix[w];
    AssociationThread[pmV, 
      (DeleteCases[fs^#, 1] &) /@ Transpose[pmm]
    ]
  ];
SetAttributes[PerfectMatchings, {Protected, ReadProtected}];


SyntaxInformation[KasteleynMatrix] = {"ArgumentsPattern" -> {_, _.}};
KasteleynMatrix[w_?ToricPotentialQ] :=
  KasteleynMatrix[w, {$x, $y}];
KasteleynMatrix[w_?ToricPotentialQ, {1|1., 1|1.}] :=
  Module[{sp, terms, k, fs, a},
    a = $a;
    sp = ExpandAll@If[AbelianPotentialQ@w,
      NonAbelianizeMesons[w], w];
    If[sp === $Failed, Return[$Failed] ];
    fs = FieldCases[sp];
    terms = GroupBy[ToricPotentialNodes[sp], Head, Keys];
    k = Outer[
      Sum[a[e] Boole@AllTrue[{##}, MemberQ@e], {e, fs}] &,
      terms[$nW], terms[$nB], 1
    ];
    Return[k];
  ];
KasteleynMatrix[w_?ToricPotentialQ, {x0_, y0_}] :=
  Module[{sp, terms, k, td, pmm, fieldPMwind, monExp, 
      solH1, solH2, fs, a, x, y, hx, hy, kast, avgExp},
    {a, x, y}  = {$a, $x, $y};
    sp = ExpandAll@If[AbelianPotentialQ@w,
      NonAbelianizeMesons[w], w];
    If[sp === $Failed, Return[$Failed] ];
    td = ToricDiagram[w];
    pmm = PerfectMatchingMatrix[w];
    fs = FieldCases[sp];
    fieldPMwind = AssociationThread[
      Sort@DeleteCases[fs^#, 1] & /@ Transpose[pmm], 
      Values@td];
    terms = GroupBy[ToricPotentialNodes[sp], Head, Keys];
    k = SparseArray@Outer[
      Sum[a[e] x^hx[e] y^hy[e] Boole@AllTrue[{##}, MemberQ@e], {e, fs}] &,
      terms[$nW], terms[$nB], 1
    ];
    monExp = First /@ GroupBy[
      MonomialList[
        ReplaceAll[HoldPattern[Times][-1, x_] :> x]@Expand@Det[k], a/@FieldCases@w],
      FieldCases -> (Exponent[#,{x,y}]&)
    ];
    solH1 = Last@Solve@KeyValueMap[(Sort[#1] /. fieldPMwind) == #2 &, monExp];
    solH2 = If[Length[solH1] == 2*Length[fs], {},
      Last@FindInstance[-1 <= (Join[hx/@fs, hy/@fs] /. solH1) <= 1, 
        Variables@Map[Last, solH1], Integers]
    ];
    kast = Normal[k] /. solH1 /. solH2;
    avgExp := Round@Mean@Flatten@Exponent[
      DeleteCases[0] /@ MonomialList[#1, {x, y, 1/x, 1/y}], #2] &;
    Map[# x^(-avgExp[#, x]) y^(-avgExp[#, y]) &, kast]
  ];
SetAttributes[KasteleynMatrix, {Protected, ReadProtected}];


translateNodes[{i_,j_}] := ReplaceAll[
  (n : $nW|$nB)[k_, {i0_, j0_}] :> n[k, {i0 + i, j0 + j}]
];
toNodeCoordinates[ndFD_, tau_] := KeyValueMap[
  Head[#1][First@#1, {i_,j_}] :> (#2 + {i,j}.tau) &, 
  ndFD
];
nodeReindex[n0_] := ReplaceAll[Join @@ Table[
  MapIndexed[nd[#1, {i_, j_}] -> nd[First@#2, {i, j}] &, 
    First /@ Select[Keys@n0, MatchQ[nd]@*Head]
  ], 
  {nd, {$nW, $nB}}]
];
edgeCentering := ReplaceAll[RuleDelayed[
    UndirectedEdge[ $nW[k_, w1_], $nB[l_, w2_] ], 
    UndirectedEdge[ $nW[k, {0, 0}], $nB[l, w2-w1] ]
  ]
];
kasteleynToEdges[kast_, Op_ : {0, 0}] :=
  Module[{dK, matMon, assoc},
    dK = Dimensions[kast];
    matMon = MonomialList[Expand@kast, $a/@FieldCases@kast];
    assoc = KeyDrop[{0, 0.}]@Flatten@MapThread[
      {x, y} |-> (Rule[#, x] & /@ y),
      {Array[{##} &, dK], matMon}, 2];
    Association@KeyValueMap[
      UndirectedEdge[
        $nW[First@#2, Op], 
        $nB[Last@#2, Op + Exponent[#1,{$x,$y}] ] 
      ] -> First@FieldCases[#1] &, 
      assoc
    ]
  ];
edgesToKasteleyn[edges_] :=
  Module[{assoc},
    assoc = KeyValueMap[
      $a[#2] Apply[Times, {$x, $y}^(#1[[2, 2]]-#1[[1, 2]])]
        -> {#1[[1, 1]], #1[[2, 1]]} &,
      edges
    ];
    Normal@SparseArray@Normal[
      Total/@GroupBy[assoc, Last -> First] 
    ]
  ];


normalizeFundDomain[{nodes_, edges_, faces_, tau_}, {xf___?FieldQ}] :=
  Module[{rotM, rotTau, sgnM, reflTau, skewness, skewTau, skewM, 
    newTau, toCoords, fixNodeWind},
    rotM = First@Keys@MinimalBy[
      AssociationMap[{#1 . tau[[1]], #1 . tau[[2]]} &,
        RotationMatrix /@ Range[0, 2 Pi, Pi/15] 
      ], {#[[1, 2]]^2, -#[[1, 1]]} &];
    rotTau = Map[rotM.# &, tau];
    sgnM = {{1, 0}, {0, Sign@rotTau[[2, 2]]}};
    reflTau = Map[sgnM.# &, rotTau];
    skewness = First[#1].Last[#1] / First[#1].First[#1] &;
    skewTau = Map[skewM.# &, reflTau];
    skewM = First@Nearest[Select[
      AssociationMap[{#1 . First[reflTau], #1 . Last[reflTau]} &,
        {{1, 0.2 #}, {0, 1}} & /@ Most@Range[-10, 10] 
      ], (skewness[#]^2 < 1/8 &)],
      reflTau, 
      DistanceFunction -> ((skewness[#1] - skewness[#2])^2 &)
    ];
    newTau = Map[skewM.# &, reflTau];
    newNodes = (skewM.sgnM.rotM.# &) /@ nodes;
    toCoords = ReplaceAll@toNodeCoordinates[newNodes, newTau];
    fixNodeWind = If[Length@{xf}<2, False, AllTrue[
      toCoords@Partition[{xf} /. KeyValueMap[#2 -> -Subtract @@ #1 &]@edges, 2, 1],
      Apply[#1 . {{0, 1}, {-1, 0}} . #2  > 0 &]
    ] ];
    MapAt[{{1,0},{0,(-1)^Boole[fixNodeWind]}} . # &, 
      {newNodes, edges, faces, newTau},
      {{1,All},{4,All}}
    ]
  ];
transformTiling[tiling0_, opt_] :=
  Module[{optSV, optRot, optSkew, optT, optSc, optTT, 
      sv, trans, transT, scale, skew, rot, mat, tau0},
    {optSV, optRot, optSkew, optT, optSc, optTT} = OptionValue[
      BraneTiling, opt,
      {"ShiftVertex", "RotateTiling", "SkewTiling", 
        "TransformMatrix", "ScaleTiling", "TranslateTiling"}
    ];
    rot = Switch[optRot,
      (_?NumericQ), RotationMatrix[optRot],
      _, IdentityMatrix[2] 
    ];
    skew = Switch[optSkew,
      {(_?NumericQ), (_?NumericQ)}, {{1, optSkew[[1]]}, {optSkew[[2]], 1}},
      _, IdentityMatrix[2] 
    ];
    scale = Switch[optSc,
      {(_?NumericQ), (_?NumericQ)}, DiagonalMatrix[optSc],
      _, IdentityMatrix[2] 
    ];
    trans = Switch[optT,
      {Repeated[{_?NumericQ, _?NumericQ}, {2}]}, optT,
      _, IdentityMatrix[2] 
    ];
    transT = Switch[optTT,
      {_?NumericQ, _?NumericQ}, Clip /@ optTT,
      _, {0,0} 
    ];
    mat = Dot[trans, scale, skew, rot];
    transF = MapAt[Map[mat . # &], {{1}, {4}}];
    tau0 = Last[tiling0];
    patt = ($nB|$nW)[_Integer] -> {_?NumberQ, _?NumberQ}; 
    sv = Switch[optSV,
      KeyValuePattern[patt], optSV,
      _, Association[] 
    ];
    shiftF = MapAt[Association@*KeyValueMap[
      #1 -> #2 + (Lookup[sv, Take[#1, 1], {0, 0}]-transT).tau0 &
    ], {{1}}];
    transF@shiftF[tiling0]
  ];


Options[BraneTiling] = {
  "ShiftVertex" -> Automatic,
  "RotateTiling" -> Automatic,
  "SkewTiling" -> Automatic,
  "ScaleTiling" -> Automatic,
  "TransformMatrix" -> Automatic,
  "Embedding" -> "SpringElectricalEmbedding",
  "EmbeddingRange" -> Automatic,
  "TranslateTiling" -> Automatic
};
SyntaxInformation[BraneTiling] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};
BraneTiling[W_?ToricPotentialQ, opts: OptionsPattern[BraneTiling] ] :=
  BraneTiling[KasteleynMatrix@W, opts];
BraneTiling[kast_?MatrixQ, opts: OptionsPattern[BraneTiling] ] :=
  Module[{embRng, Imin, Imax, Jmin, Jmax, edges0, gr0, coordV, c0, fdL, xx,
      yy, tau, faceSelF, faces, potWTerm, tiling},
    embRng = OptionValue["EmbeddingRange"];
    {{Imin, Imax}, {Jmin, Jmax}} = Switch[embRng,
      i_Integer?(GreaterThan[1]),
      {{-1,1},{-1,1}} embRng,
      {m_Integer,M_Integer} /; m<=M,
      {embRng, embRng},
      {{im_Integer,iM_Integer}/;(im<iM), {jm_Integer,jM_Integer}/;(jm<jM)},
      embRng,
      _, {{-2,2},{-2,2}}
    ];
    ndFDPatt = ($nW|$nB)[_, {0, 0}];
    edges0 = Table[kasteleynToEdges[kast, {i,j}], 
      {i,Imin,Imax}, {j,Jmin,Jmax}];
    gr0 = Graph[Flatten@Map[Keys, edges0, {2}],
      GraphLayout -> OptionValue["Embedding"] ];
    coordV = AssociationThread[VertexList@gr0, 
      VertexCoordinates/.AbsoluteOptions[gr0]
    ];
    c0 = Mean@Values@KeySelect[coordV, MatchQ@ndFDPatt];
    groupedV = KeySort /@ KeySelect[
      GroupBy[Normal@Map[#-c0 &, coordV], Last@*First], 
      MatchQ[{(-1|0|1) ..}]
    ];
    fdL = DeleteCases[{0, 0}]@Tuples[{-1, 0, 1}, 2];
    xx = Join @@ Map[Table[#, Length@groupedV@#] &, fdL];
    yy = Join @@ Table[Values@groupedV[p] - Values@groupedV[{0, 0}], {p,fdL}];
    tau = Inverse[Transpose[xx].xx].Transpose[xx].yy;

    faceSelF[i_] := Select[MatchQ[ Subscript[X,_][i,_] | Subscript[X,_][_,i] ] ];
    edgeRng = Take[edges0, Sequence@@Map[#+{-1,1} &]@Ceiling[Dimensions[edges0]/2] ];
    faces = Association@Map[
      DeleteCases[_?AcyclicGraphQ]@ConnectedGraphComponents[
        Keys@faceSelF[#]@Apply[Join]@Flatten@edgeRng
      ] -> # &,
      Sort@DeleteDuplicates@Flatten[List @@@ FieldCases@kast]
    ] // KeyMap[ First@*FindCycle@*EdgeList@*Last@*SortBy[Count[ndFDPatt]@*VertexList] ];

    potWTerm = QuiverFromFields@DeleteCases[First[kast]/.{$x|$y->1,$a->Identity}, 0] //
      ReplaceAll[KeyValueMap[Reverse@*Rule]@#]@First@ReorderLoopEdges@Values[#] &;
    tiling = normalizeFundDomain[
      {groupedV[{0,0}], edgeRng[[2,2]], <|faces|>, tau},
      potWTerm
    ];
    transformTiling[tiling, {opts}]
  ];
SetAttributes[BraneTiling, {Protected, ReadProtected}];


SyntaxInformation[IntegrateOutTiling] = {"ArgumentsPattern" -> {_, _, _.}};
IntegrateOutTiling[tiling0_, mterm : HoldPattern[CenterDot|List][_?FieldQ,_?FieldQ] ] :=
  Module[{nd, vx, fc, tau, toCoords, take1, termE, pos, centeredE, cP,
      newN, rule, tiling},
    {nd, vx, fc, tau} = tiling0;
    take1 = Take[#, 1] &;
    toCoords = ReplaceAll@toNodeCoordinates[nd, tau];
    termE = Keys@Select[vx, MatchQ[Alternatives @@ mterm] ];
    pos = First@FirstPosition[
      SameQ @@@ Transpose@Map[take1, List @@@ termE, {2}], True];
    centeredE = Map[MapAt[x |-> x - #[[pos, 2]], {All, 2}]@# &]@termE;
    newN = take1@First@MaximalBy[VertexList@centeredE, {Head@#, -First@#} &];
    cP = Append[newN, {0, 0}] -> Mean@toCoords@VertexList@centeredE;
    rule = ReplaceAll@Map[
      Append[take1@#, {i_, j_}] -> Append[newN, {i, j} - Last@#] &,
      VertexList@centeredE];
    tiling = {
      KeySort@Join[<|cP|>, KeySelect[MatchQ[Except@newN]@*take1@*rule]@nd],
      KeyMap[rule, Select[vx, MatchQ@Except[Alternatives @@ mterm] ] ],
      KeyMap[DeleteCases[ UndirectedEdge[x_, x_] ]@*rule, fc],
      tau
    };
    MapAt[KeyMap[edgeCentering], {{2}}]@MapAt[
      KeyMap[ nodeReindex[First@tiling] ], tiling, {{1}, {2}, {3}}]
  ];
IntegrateOutTiling[tiling_, mterm : HoldPattern[CenterDot|List][_?FieldQ,_?FieldQ], t0 : (_?NumberQ)] :=
  Module[{take1, nd, vx, fc, tau, toCoords, termE, pos, centeredE, cP, 
      shifts, t},
    take1 = Take[#, 1] &;
    {nd, vx, fc, tau} = tiling;
    toCoords = ReplaceAll@toNodeCoordinates[nd, tau];
    termE = Keys@Select[vx, MatchQ[Alternatives @@ mterm] ];
    pos = First@FirstPosition[
      SameQ @@@ Transpose@Map[take1, List @@@ termE, {2}], True];
    centeredE = Map[MapAt[x |-> x - #[[pos, 2]], {All, 2}]@# &]@termE;
    cP = Mean@toCoords@VertexList@centeredE;
    shifts = KeyMap[take1]@AssociationMap[(toCoords@# - cP) &, 
      VertexList@centeredE];
    t = Switch[t0, x_ /; x > 1, 1, x_ /; x < -1, -1, _, t0]; 
    MapAt[Association@*KeyValueMap[
      #1 -> #2 - t Lookup[shifts, Take[#1, 1], {0, 0}] &], tiling, {{1}}]
  ];
SetAttributes[IntegrateOutTiling, {Protected, ReadProtected}];


Options[BraneTilingGraph] = Normal@Association@{
  Splice@Options[Graphics],
  Splice@Options[BraneTiling],
  ImageSize -> Automatic,
  PlotRange -> Automatic,
  EdgeStyle -> Directive[ Black, AbsoluteThickness[2] ],
  "FaceStyle" -> Automatic,
  "FaceLabels" -> Automatic,
  "FaceLabelsStyle" -> Directive[FontSize->18, FontWeight->"SemiBold"],
  VertexStyle -> { 
    $nW[_] -> Directive[ FaceForm[White], EdgeForm[{Black, AbsoluteThickness[2]}] ],
    $nB[_] -> Directive[ FaceForm[Black], EdgeForm[{Black, AbsoluteThickness[2]}] ]
  },
  "ZigZags" -> None,
  "ZigZagsStyle" -> Directive[AbsoluteThickness[1.35], Arrowheads[{{0.018, 0.33}, {0.018, 0.85}}] ],
  "ZigZagsFunction" -> Arrow@*(TwistedZigZag[#,0.08]&)
};
SyntaxInformation[BraneTilingGraph] = {"ArgumentsPattern" -> {_, _., OptionsPattern[]}};
BraneTilingGraph[arg : (_List| _?ToricPotentialQ), opts : OptionsPattern[BraneTilingGraph] ] :=
  BraneTilingGraph[arg, Automatic, opts];
BraneTilingGraph[arg : (_List| _?ToricPotentialQ), Automatic, opts : OptionsPattern[BraneTilingGraph] ] :=
  BraneTilingGraph[arg, {{-2,2},{-2,2}}, opts];
BraneTilingGraph[W_?ToricPotentialQ, {{im_,iM_},{jm_,jM_}}, opts : OptionsPattern[BraneTilingGraph] ] :=
  BraneTilingGraph[
    BraneTiling[W, Sequence @@ FilterRules[{opts}, {"Embedding", "EmbeddingRange"}] ], 
    {{im,iM},{jm,jM}}, opts];
BraneTilingGraph[tiling0 : {_,_,_,_}, {{im_,iM_},{jm_,jM_}}, opts : OptionsPattern[BraneTilingGraph] ] :=
  Module[{optsBT, optsBTG, optsGR, nodes0, edges0, faces0, tau0, toCoords, 
      nodes, edges, faces, FDrect, grRange, faceGr, faceLblGr, edgeGr, zigzagGr, nodeGr},
    optsBT = FilterRules[{opts}, Options@BraneTiling];
    optsBTG = FilterRules[{opts}, Options@BraneTilingGraph];
    optsGR = FilterRules[{opts}, Except[
      Union[Options@BraneTilingGraph,Options@BraneTiling], Options@Graphics]
    ];
    
    {nodes0, edges0, faces0, tau0} = transformTiling[tiling0, optsBT];
    toCoords = ReplaceAll@toNodeCoordinates[nodes0, tau0];

    nodes = Flatten@Table[translateNodes[{i,j}]@Keys@nodes0, 
      {i,Min[-2,im], Max[2,iM]}, {j,Min[-2,jm], Max[2,jM]}];
    edges = Join @@ Flatten@Table[KeyMap[translateNodes[{i,j}], edges0], 
      {i,Min[-2,im], Max[2,iM]}, {j,Min[-2,jm], Max[2,jM]}];
    faces = Join @@ Flatten@Table[KeyMap[translateNodes[{i,j}], faces0], 
      {i,Min[-2,im], Max[2,iM]}, {j,Min[-2,jm], Max[2,jM]}];

    FDrect = {{-1, -1}, {1, -1}, {1, 1}, {-1, 1}}/2;
    grRange = FDrect.(tau0 + 0.7*Min[Norm/@tau0]*Map[Normalize,tau0]);

    {faceGr, faceLblGr} = tilingFaceGraphics[KeyMap[toCoords]@faces, optsBTG];
    edgeGr = tilingEdgeGraphics[KeyMap[toCoords]@edges, optsBTG];
    zigzagGr = tilingZigZagGraphics[edges, toCoords, optsBTG];
    nodeGr = tilingNodeGraphics[AssociationMap[toCoords]@nodes, optsBTG];
    Graphics[{
      faceGr, edgeGr, zigzagGr, nodeGr, faceLblGr,
      {EdgeForm[{Dashed, Black}], FaceForm[Transparent], Polygon[FDrect.tau0]}},
      Sequence @@ optsGR,
      PlotRange -> Switch[OptionValue["PlotRange"],
        Automatic, Map[MinMax, Transpose[grRange] ],
        _, OptionValue["PlotRange"]
      ],
      ImageSize -> Switch[OptionValue["ImageSize"],
        Automatic, UpTo[450],
        _, OptionValue["ImageSize"]
      ]
    ] 
  ];
SetAttributes[BraneTilingGraph, {Protected, ReadProtected}];


tilingEdgeGraphics[edgesA_, opts : OptionsPattern[BraneTilingGraph] ] :=
  Module[{opt, def, dirParse, rules},
    def = OptionValue[BraneTilingGraph, Options[BraneTilingGraph], EdgeStyle];
    opt = OptionValue[BraneTilingGraph, opts, EdgeStyle];
    dirParse = If[MatchQ[#1, None | Directive[None] ], 
      Directive[None], Flatten@Directive@#1 ] &;
    rules = Cases[Normal@opt, HoldPattern[Rule][f_?(Not@*FreeQ[X]), d_] :> If[
      FreeQ[f,_?FieldQ], Rule[f, dirParse@d], 
      Splice@Thread[FieldCases[{f}]-> dirParse@d] ]
    ];
    Switch[Normal@opt,
      Automatic | All | True, 
      Return[{def, KeyValueMap[{Line@*List @@ #1} &, edgesA]}],
      None | Directive[None] | False,
      Return[{}],
      KeyValuePattern[{}],
      Return[{def, KeyValueMap[{#2/.rules/.{(_?FieldQ)->Nothing}, 
        Line@*List @@ #1} &, edgesA]}],
      _, 
      Return[{Directive[opt], KeyValueMap[{Line@*List @@ #1} &, edgesA]}]
    ]
  ];
tilingFaceGraphics[facesA_, opts : OptionsPattern[BraneTilingGraph] ] :=
  Module[{faces, facePatt, defLblS, optS, optLbl, optLblS, fcLbl,
      fcLblS, dirParse, faceGrF},
    faces = Alternatives @@ Sort@DeleteDuplicates[Values@facesA];
    facePatt = Join[faces, Alternatives@HoldPattern[Alternatives][(faces) ..] ];
    defLblS = OptionValue[BraneTilingGraph, Options[BraneTilingGraph], 
      "FaceLabelsStyle"];
    {optS, optLbl, optLblS} = OptionValue[BraneTilingGraph, opts, 
      {"FaceStyle", "FaceLabels", "FaceLabelsStyle"}];
    dirParse = If[MatchQ[#1, None | Directive[None] ], 
      Directive[EdgeForm@None, FaceForm@None], Flatten@Directive@#1 ] &;
    (* face polygons *)
    faceGrF = (Polygon@Join[First/@Most@#1, List@@Last@#1] &);
    faceGrMap = {Directive[EdgeForm@None, FaceForm@None],
      KeyValueMap[{x,y}|->{Lookup[#,y,Nothing], faceGrF[x]}, facesA]} &;
    faceGr = Switch[Normal@optS,
      Automatic | None | False | Directive[None], {},
      KeyValuePattern[{}], 
      faceGrMap@Association@Cases[
        Normal@optS, HoldPattern[Rule][f_: facePatt, d_] 
          :> Splice@Thread@Rule[UniqueCases[{f},faces], dirParse@d]
      ],
      _, {Flatten@Directive@optS, Map[faceGrF, Keys@facesA]}
    ];
    (* face labels *)
    fcLbl = Switch[Normal@optLbl,
      All | Automatic | True, AssociationThread[List@@faces, List@@faces],
      {__}, Join[
        (AssociationThread[#,#] &)@UniqueCases[{Normal@optLbl},faces],
        Association@Cases[Normal@optLbl, HoldPattern[Rule][faces, _] ]
      ],
      _ , <||>
    ];
    fcLblS = Switch[Normal@optLblS,
      Automatic, 
      Association@Thread@Rule[List@@faces, defLblS],
      KeyValuePattern[{}], 
      Join[Association@Thread@Rule[List@@faces, defLblS],
        Association@Cases[Normal@optLbl, HoldPattern[Rule][f: facePatt, d_] 
          :> Splice@Thread[UniqueCases[{f},faces] -> d] ]
      ],
      _ , Association@Thread@Rule[List@@ faces, Flatten@Directive@Normal@optLblS]
    ];
    faceLblGrF = (Text[Style[fcLbl@#2, fcLblS@#2], Mean@VertexList@#1] &);
    faceLblGr = KeyValueMap[faceLblGrF]@Select[facesA, MatchQ[Alternatives @@ Keys@fcLbl] ];
    {faceGr, faceLblGr}
  ];
tilingNodeGraphics[nodeA_, opts : OptionsPattern[BraneTilingGraph] ] :=
  Module[{opt, def, dirParse, rules},
    def = OptionValue[BraneTilingGraph, Options[BraneTilingGraph], VertexStyle];
    opt = OptionValue[BraneTilingGraph, opts, VertexStyle];
    dirParse = If[MatchQ[#1, None | Directive[None] ], 
      Directive[EdgeForm@None,FaceForm@None], 
      Flatten@Directive@#1 ] &;
    rules = Cases[Normal@opt, 
      HoldPattern[Rule][n_?(Not@*FreeQ[$nW|$nB]), d_] 
        :> Rule[n, dirParse@d]
    ];
    Switch[Normal@opt,
      None | Directive[None] | False,
      Return[{}],
      KeyValuePattern[{}],
      Return@KeyValueMap[{Take[#1,1]/.rules/.def, Disk[#2, 1/12]} &, nodeA],
      _, 
      Return@KeyValueMap[{Take[#1,1]/.def, Disk[#2, 1/12]} &, nodeA]
    ]
  ];
tilingZigZagGraphics[edgesA_, toCoords_, opts : OptionsPattern[BraneTilingGraph] ] :=
  Module[{opt, optS, optF, zzs, zzQ},
    {opt, optS, optF} = OptionValue[BraneTilingGraph, opts, 
      {"ZigZags", "ZigZagsStyle", "ZigZagsFunction"}];
    zzQ = And[FieldProductQ@#,GaugeInvariantQ@#] &;
    zzs = Join[
      Association@Cases[Normal@opt, 
        HoldPattern[Rule][z_?(zzQ),d_] :> Rule[z, Flatten@Directive@d]
      ],
      Cases[Normal@opt, _?(zzQ)] // AssociationThread[#,
        ColorData[97] /@ Range@Length@#] &
    ];
    {optS, KeyValueMap[{Flatten@Directive@#2,
      optF/@toCoords@zigZagEdges[edgesA, List@@#1]} &]@zzs}
  ];
zigZagEdges[edges_, f_] :=
  Module[{lines, fWN, linesToWN, lineToNd, groups, paths, ndOrder},
    linesToWN = Total[First@*Differences@*Map[Last]@*List @@@ #] &;
    lineToNd = ReplaceAll[(n:$nW|$nB)[k_,_] :> n@k]@Join[First/@Most@#, Last@#] &;
    lines = Select[edges, MatchQ[Alternatives @@ f] ];
    fWN = Apply[List,f] /.KeyValueMap[Reverse@*Rule,lines] // 
      MapAt[Reverse, #, List /@ 
        Range[If[#[[1,1,1]] === #[[2,1,1]], 1, 2], Length@#, 2]
      ] & // linesToWN;
    groups = Select[PathGraphQ]@ConnectedGraphComponents[Keys@lines];
    paths = MapThread[
      Partition[First@FindPath[#1,First@#2,Last@#2],2,1] &,
      {groups, GraphPeriphery /@ groups}
    ] // Map[If[fWN.linesToWN[#] < 0, Map[Reverse,#,{0,1}], #] &];
    ndOrder = Select[paths, fWN.linesToWN[#] !=0 &] //
      lineToNd@*First@*MaximalBy[Length];
    If[{SequenceCount[ndOrder, lineToNd@#], fWN.linesToWN[#]} === {0,0}, 
      Map[Reverse,#,{0,1}], #] & /@ paths
  ];


primF_[ TwistedZigZag[{{}...}, _] ] ^:= primF[{{}}] /; 
  MatchQ[primF, Line | Arrow | BSplineCurve | BezierCurve];
primF_[ TwistedZigZag[lines_, d_ : 0.1] ] ^:= 
  Module[{pts, vs, ls, ts, ns, sgn, gs}, 
    pts = Join[lines[[{1}, 1]], lines[[All, 2]]];
    vs = Differences[pts];
    ls = Map[Norm, vs];
    ts = Map[Normalize, vs];
    ns = Map[RotationTransform[-Pi/2], ts];
    gs = MapThread[
      If[PossibleZeroQ[#1 . #2], 0, (#2 . #2)/(#1 . #2)] &, 
      {Most[ns] + Rest[ns], Rest[ts] - Most[ts]}
    ] // Join[{-Sign@First[#,1]}, #, {-Sign@Last[#,1]}] &;
    sgn = Sign[First@gs] (-1)^Range[2, Length@gs];
    Map[primF]@Transpose[{
      Most[pts] + d sgn ns + Most[Abs@gs] Abs[d] ts,
      Most[pts] + d sgn ns + (ls/2 - Abs[d]) ts, 
      Most[pts] - d sgn ns + (ls/2 + Abs[d]) ts, 
      Rest[pts] - d sgn ns - Rest[Abs@gs] Abs[d] ts
    }]
  ] /; MatchQ[primF, Line | Arrow | BSplineCurve | BezierCurve];



$termsZagHN[i_, j_, g_, M_] := {
  $nW[i, j] -> CenterDot[
    X[g[i, j], g[i - 1, j], M], X[g[i - 1, j], g[i, j - 1], M@0], X[g[i, j - 1], g[i, j], M]
  ],
  $nB[i, j] -> CenterDot[
    X[g[i, j - 1], g[i - 1, j - 1], M], X[g[i - 1, j - 1], g[i - 1, j], M], X[g[i - 1, j], g[i, j - 1], M@0]
  ]
};
$termsZigHN[i_, j_, g_, M_] := {
  $nW[i, j] -> CenterDot[
    X[g[i, j - 1], g[i - 1, j - 1], M], X[g[i - 1, j - 1], g[i - 1, j], M], X[g[i - 1, j], g[i, j - 1], M@0]
  ], 
  $nB[i, j] -> CenterDot[
    X[g[i, j], g[i - 1, j], M], X[g[i - 1, j], g[i, j - 1], M@0], X[g[i, j - 1], g[i, j], M]
  ]
};
$termsZig2[i_, j_, g_, M_] := {
  $nW[i, j] -> CenterDot[
    X[g[i, j - 1], g[i - 1, j - 1], M], X[g[i - 1, j - 1], g[i, j], M@0], X[g[i, j], g[i, j - 1], M]
  ], 
  $nB[i, j] -> CenterDot[
    X[g[i, j], g[i - 1, j], M], X[g[i - 1, j], g[i - 1, j - 1], M], X[g[i - 1, j - 1], g[i, j], M@0]
  ]
};
$termsZag2[i_, j_, g_, M_] := {
  $nW[i, j] -> CenterDot[
    X[g[i, j], g[i - 1, j], M], X[g[i - 1, j], g[i - 1, j - 1], M], X[g[i - 1, j - 1], g[i, j], M@0]
  ], 
  $nB[i, j] -> CenterDot[
    X[g[i, j - 1], g[i - 1, j - 1], M], X[g[i - 1, j - 1], g[i, j], M@0], X[g[i, j], g[i, j - 1], M]
  ]
};

Options[ZigZagDeformation] = {Method -> Automatic};
ZigZagDeformation[
  w_?ToricPotentialQ, zzPath_?PossibleMesonQ, 
  k : (_Integer?Positive) : 1,
  opts : OptionsPattern[ZigZagDeformation]
] /; ZigZagPathQ[zzPath, w] :=
  Module[{g, m, method, terms, v, n, ord, nodes, ffNodes, zz, gRules, nodeFromPair, newNodes},
    {g, m} = {\[FormalCapitalG], \[FormalM]};
    {method, terms} = Switch[OptionValue[Method],
      "ZigHN", {1, $termsZigHN},
      "ZagHN", {-1, $termsZagHN},
      "Zig", {1, $termsZig2},
      "Zag", {-1, $termsZag2},
      _, {1, $termsZigHN}
    ];
    v = (Max[Length[#1], Max[#1]] &)@VertexList@Values@QuiverFromFields[w];
    n = Length[zzPath]/2; 
    ord = ZigZagOrderings[w, zzPath]; 
    nodes = KeyValueReverse@ToricPotentialNodes[w]; 
    ffNodes = AssociationMap[
      Sort@Keys@Select[nodes, ContainsQ@#1] &, 
      FieldCases@w
    ];
    zz = Reverse@MapApply[UndirectedEdge]@MapAt[Reverse,
      AssociationMap[Lookup[ffNodes, #1] &, List @@ If[First[ord] == method, RotateLeft@zzPath, zzPath]],
      Table[{i}, {i, 1 + Boole[method == 1], 2 n, 2}]
    ];
    nodeFromPair[x_] := (First[Pick[VertexList[#1], VertexDegree[#1], 2]] &)@Values[x]; 
    gRules = Union @@ Table[
      Thread[{g[Mod[i, n, 1], 0], g[Mod[i, n, 1], k]} -> 
        List @@ Keys[zz][[Mod[2 i, 2 n, 1]]]
      ], {i, 1, n}];
    gRules = Join[gRules, 
      MapIndexed[#1 -> (v + First@#2) &,
        Union@Flatten@Table[g[Mod[i, n, 1], Mod[j, k + 1]], {i, 1, n}, {j, 1, k - 1}]
      ]
    ];
    newNodes = Flatten@Table[
      MapThread[
        nodeFromPair[#1] -> CenterDot[Fold[DG, nodes@nodeFromPair@#1, Keys@#1], #2] &,
        {{zz[[Mod[{2 i, 2 i + 1}, 2 n, 1]]], zz[[Mod[{2 i - 1, 2 i}, 2 n, 1]]]},
         {X[g[i + 1, k], g[i, k], M], X[g[i, 0], g[i - 1, 0], M]}}
      ],
      {i, 1, n}
    ];
    newNodes = Join[newNodes,
      Flatten@Table[terms[i, j, g, m], {j, 1, k}, {i, 1, n}]
    ] /. {g[i_, j_] :> g[Mod[i, n, 1], Mod[j, k + 1]]} /. gRules;
    nodes = Append[nodes, newNodes];
    RelabelFieldMultiplicity@Total@KeyValueMap[(2 Boole[MatchQ[_$nW][#1]] - 1) #2 &, nodes]
  ];
SetAttributes[ZigZagDeformation, {Protected, ReadProtected}];


ZigDeformation[
  w_?ToricPotentialQ, zzPath_?PossibleMesonQ, 
  k : (_Integer?Positive) : 1,
  opts : OptionsPattern[Normal@KeyDrop[Method]@Options@ZigZagDeformation]
] := ZigZagDeformation[w, zzPath, k, Method -> "ZigHN"];
ZagDeformation[
  w_?ToricPotentialQ, zzPath_?PossibleMesonQ, 
  k : (_Integer?Positive) : 1,
  opts : OptionsPattern[Normal@KeyDrop[Method]@Options@ZigZagDeformation]
] := ZigZagDeformation[w, zzPath, k, Method -> "ZagHN"];
SetAttributes[ZigDeformation, {Protected, ReadProtected}];
SetAttributes[ZagDeformation, {Protected, ReadProtected}];


ContractDigons[w_?PotentialQ] :=
  Module[{qinc},
    qinc = AssociationThread[
      Sort@VertexList@Values@QuiverFromFields[w],
      QuiverIncidenceMatrix[w]
    ];
    Simplify@Fold[
      RelabelFieldMultiplicity@ReplaceAll[
        HoldPattern[CenterDot][
          CyclicPatternSequence[l___, Subscript[X, 1][i_, #2], Subscript[X, 1][#2, j_], r___]
        ] :> CenterDot[l, X[i, j, \[FormalM]@#2], r]
      ][#1] &,
      w,
      Keys@Select[qinc, Total[#] == 0 && Total@Abs[#] == 2 &]
    ]
  ];
SetAttributes[ContractDigons, {Protected, ReadProtected}];


End[]

EndPackage[]
