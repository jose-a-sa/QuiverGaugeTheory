BeginPackage["QuiverGaugeTheory`Tiling`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`", 
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Polytope`"
}]


PerfectMatchingMatrix::usage = "";
KasteleynMatrix::usage = "";
BraneTiling::usage = "";
BraneTilingGraph::usage = "";


Begin["`Private`"]


$grRng = 2;
$a = \[FormalA];
$x = \[FormalX];
$y = \[FormalY];
$nW = \[FormalW];
$nB = \[FormalB];


SyntaxInformation[PerfectMatchingMatrix] = {"ArgumentsPattern" -> {_}};
PerfectMatchingMatrix[W_?ToricPotentialQ] :=
  Module[{k, fs, pmList, a = $a},
    fs = Fields[W];
    k = KasteleynMatrix[W, {1, 1}];
    pmList = MonomialList[Expand@Permanent[k], a/@Fields@W] // 
      ReplaceAll[a -> Identity]; 
    Boole@Outer[
      MemberQ[#2, #1] &, fs, (Alternatives @@@ pmList), 1
    ]
  ];


SyntaxInformation[KasteleynMatrix] = {"ArgumentsPattern" -> {_, _.}};
KasteleynMatrix[W_?ToricPotentialQ] :=
  KasteleynMatrix[W, {$x, $y}];
KasteleynMatrix[W_?ToricPotentialQ, {1|1., 1|1.}] :=
  Module[{sp, terms, k, fs, a},
    a = $a;
    sp = ExpandAll@If[AbelianPotentialQ@W,
      NonAbelianizeMesons[W], W];
    If[sp === $Failed, Return[$Failed] ];
    fs = Fields[sp];
    terms = GroupBy[
      Cases[sp, HoldPattern[Times][x_.,c_?FieldProductQ] :> {x, c}],
      First -> Last
    ];
    k = Outer[
      Sum[a[e] Boole@AllTrue[{##}, MemberQ@e], {e, fs}] &,
      terms[1], terms[-1], 1
    ];
    Return[k];
  ];
KasteleynMatrix[W_?ToricPotentialQ, {x0_, y0_}] :=
  Module[{sp, terms, k, td, P, fieldPMwind, monExp, solH,
      fs, a, x, y, hx, hy},
    {a, x, y}  = {$a, $x, $y};
    sp = ExpandAll@If[AbelianPotentialQ@W,
      NonAbelianizeMesons[W], W];
    If[sp === $Failed, Return[$Failed] ];
    td = ToricDiagram[W];
    P = PerfectMatchingMatrix[W];
    fs = Fields[sp];
    fieldPMwind = AssociationThread[
      Sort@DeleteCases[fs^#, 1] & /@ Transpose[P], 
      Values@td];
    terms = GroupBy[
      Cases[sp, HoldPattern[Times][x_.,c_?FieldProductQ] :> {x, c}],
      First -> Last
    ];
    k = Outer[
      Sum[a[e] x^hx[e] y^hy[e] Boole@AllTrue[{##}, MemberQ@e], {e, fs}] &,
      terms[1], terms[-1], 1
    ];
    monExp = First /@ GroupBy[
      MonomialList[Expand@Permanent[k], a/@Fields@W],
      Fields -> (Exponent[#,{x,y}]&)
    ];
    solH = Last@FindInstance[
      And@@KeyValueMap[(Sort[#1]/.fieldPMwind) == #2 &, monExp],
      Variables[Values@monExp],
      Integers
    ];
    k/.solH/.{x->x0,y->y0}
  ];


kasteleynToEdges[kast_, Op_ : {0, 0}] :=
  Module[{dK, matMon, assoc},
    dK = Dimensions[kast];
    matMon = MonomialList[Expand@kast, $a/@Fields@kast];
    assoc = KeyDrop[{0, 0.}]@Flatten@MapThread[
      {x, y} |-> (Rule[#, x] & /@ y),
      {Array[{##} &, dK], matMon}, 2];
    Association@KeyValueMap[
      UndirectedEdge[
        $nW[First@#2, Op], 
        $nB[Last@#2, Op + Exponent[#1,{$x,$y}] ] 
      ] -> First@Fields[#1] &, 
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
      Total /@ GroupBy[assoc, Last -> First] 
    ]
  ];


BraneTiling[W_?ToricPotentialQ] :=
  BraneTiling[KasteleynMatrix@W];
BraneTiling[kast_?MatrixQ] :=
  Module[{L = $grRng, edges0, gr0, coordV, c0, fdL, 
      xx, yy, tau, faceSelF, faces},
    ndFDPatt = ($nW|$nB)[_, {0, 0}];
    edges0 = Table[kasteleynToEdges[kast, {i,j}], {i, -L, L}, {j, -L, L}];
    gr0 = Graph@Flatten@Map[Keys, edges0, {2}];
    coordV = AssociationThread[
      VertexList@gr0, 
      VertexCoordinates/.AbsoluteOptions[gr0]
    ];
    c0 = Values@KeySelect[coordV, MatchQ[ndFDPatt] ] // Mean;
      (* First@Nearest[#, Mean@#, DistanceFunction->EuclideanDistance] &; *)
    groupedV = KeySort /@ KeySelect[
      GroupBy[Normal@Map[#-c0 &, coordV], Last@*First], 
      MatchQ[{(-1|0|1) ..}]
    ];
    fdL = DeleteCases[{0, 0}]@Tuples[{-1, 0, 1}, 2];
    xx = Join @@ Map[Table[#, Length@groupedV@#] &, fdL];
    yy = Join @@ Table[ Values@groupedV[p]-Values@groupedV[{0, 0}], {p, fdL}];
    tau = Inverse[Transpose[xx].xx].Transpose[xx].yy;
    faceSelF[i_] := Select[MatchQ[ Subscript[X,_][i,_] | Subscript[X,_][_,i] ] ];
    faces = Table[
      EdgeList@First@MaximalBy[
        Select[Not@*AcyclicGraphQ]@ConnectedGraphComponents[
          Keys@faceSelF[i]@Apply[Join]@Flatten[ edges0[[{0,1,2}+L,{0,1,2}+L]] ] 
        ], 
        Count[ndFDPatt]@*VertexList
      ] -> i,
      {i, Sort@DeleteDuplicates@Flatten[List @@@ Fields@kast]}
    ];
    {
      groupedV[{0,0}], 
      edges0[[L+1,L+1]], 
      <|faces|>,
      tau
    }
  ];

Select[{Partition[#,2,1],Partition[Reverse@#,2,1]}, 
        (linesToWN[#].fieldWN)/(fieldWN.fieldWN) >0 & ] &;

zigZagEdges[edges_, f_] :=
  Module[{lines, fWN, linesToWN, lineToNd, groups, paths, ndOrder},
    linesToWN = Total[First@*Differences@*Map[Last]@*List @@@ #] &;
    lineToNd = ReplaceAll[(n:$nW|$nB)[k_,_] :> n@k]@Join[First/@Most@#, Last@#] &;
    lines = Select[edges, MatchQ[Alternatives @@ f] ];
    fWN = Apply[List,f] /.KeyValueMap[Reverse@*Rule,lines] // 
      MapAt[Reverse, #, List /@ 
        Range[If[#[[1,1,1]] === #[[2,1,1]], 1, 2], Length@#, 2]
      ] & // linesToWN;
    groups = Select[Keys@lines, Not@*FreeQ[Alternatives @@ #] ] & /@ 
      ConnectedComponents[Keys@lines];
    paths = MapThread[
      Partition[First@FindPath[#1,First@#2,Last@#2],2,1] &,
      {groups, GraphPeriphery /@ groups}
    ] // Map[If[fWN.linesToWN[#] > 0, Map[Reverse,#,{0,1}], #] &];
    ndOrder = lineToNd@First@MaximalBy[
      Select[paths, fWN.linesToWN[#] !=0 &], Length];
    Map[If[0 == SequenceCount[ndOrder, lineToNd@#], 
      Map[Reverse,#,{0,1}], #] &, paths]
  ];
twistedZigZagArrows[{{}...}, _] := {{}};
twistedZigZagArrows[lines_, d_ : 0.1] := 
  Module[{pts, vs, ls, ts, ns, sgn, gs, arrows},
    pts = Join[lines[[{1}, 1]], lines[[All, 2]]];
    vs = Differences[pts];
    ls = Map[Norm, vs];
    ts = Map[Normalize, vs];
    ns = Map[RotationTransform[-Pi/2], ts];
    gs = MapThread[If[PossibleZeroQ[#1 . #2], 0, #2 . #2/#1 . #2] &,
      {Most[ns] + Rest[ns], Rest[ts] - Most[ts]}
    ] // Join[{-Sign@First@#}, #, {-Sign@Last@#}] &;
    sgn = Most[Sign@gs];
    arrows = Transpose[{
      Most[pts] + d sgn ns + Most[Abs@gs] Abs[d] ts,
      Most[pts] + d sgn ns + (ls/2 - Abs[d]) ts,
      Most[pts] - d sgn ns + (ls/2 + Abs[d]) ts,
      Rest[pts] - d sgn ns - Rest[Abs@gs] Abs[d] ts
    }]
  ];


BraneTilingGraph[arg : (_List| _?ToricPotentialQ), {{im_,iM_},{jm_,jM_}}] :=
  BraneTilingGraph[arg, {{im,iM},{jm,jM}}, {}];
BraneTilingGraph[W_?ToricPotentialQ, {{im_,iM_},{jm_,jM_}}, zzs0_] :=
  BraneTilingGraph[BraneTiling@W, {{im,iM},{jm,jM}}, Flatten@{zzs0}];
BraneTilingGraph[{nodes0_, edges0_, faces0_, tau_}, {{im_,iM_},{jm_,jM_}}, zzs0_] :=
  Module[{translate, toCoords, nodes, arrowStyle, zigzagG,
      sc, nodebG, nodewG, lineG, textG, FDrect, zzs},
    translate[{i_,j_}] := ReplaceAll[
      (n : $nW|$nB)[k_, {i0_, j0_}] :> n[k, {i0 + i, j0 + j}]
    ];
    toCoords = ReplaceAll@KeyValueMap[
      Head[#1][First@#1, {i_,j_}] :> (#2 + {i,j}.tau) &,
      nodes0
    ];
    nodes = GroupBy[Head]@Flatten@Table[
      translate[{i,j}]@Keys@nodes0, {i,im,iM}, {j,jm,jM}];
    edges = Join @@ Flatten@Table[
      KeyMap[translate[{i,j}], edges0], {i,im,iM}, {j,jm,jM}];
    faces = Join @@ Flatten@Table[
      KeyMap[translate[{i,j}], faces0], {i,im,iM}, {j,jm,jM}];
    zzs = Flatten[{zzs0}];

    sc = 0.002;
    nodebG = {FaceForm[Black], EdgeForm[{Black, AbsoluteThickness[2]}],
      Disk[#, 1/12]} &;
    nodewG = {FaceForm[White], EdgeForm[{Black, AbsoluteThickness[2]}],
      Disk[#, 1/12]} &;
    lineG = {Black, AbsoluteThickness[2], Line@#} &;
    textG = Text[Style[#, 16, FontWeight->"SemiBold"], #2] &;
    arrowStyle = Arrowheads[{{6 sc, 0.33}, {6 sc, 0.85}}];
    zigzagG = {AbsoluteThickness[1.2], arrowStyle, Splice[Arrow /@ #]} &;
    
    FDrect = {{0,0}, {1,0}, {1,1}, {0,1}} - 0.50*Table[{1,1},4];

    Graphics[{
      (lineG@*List @@@ toCoords@Keys@edges),
      MapThread[
        {#2, Map[x |-> zigzagG@twistedZigZagArrows[x, 0.08], 
          toCoords@zigZagEdges[edges, #1] ]} &, 
        {zzs, Switch[Length@zzs, 
          0, {}, 1, {ColorData["Rainbow"][1]},
          _, ColorData["Rainbow"] /@ Range[0,1,1/(Length@zzs-1)] 
        ]}
      ],
      Join[nodebG /@ toCoords@nodes@$nB, nodewG /@ toCoords@nodes@$nW],
      KeyValueMap[textG[#2, Mean@#1] &]@KeyMap[toCoords@*VertexList, faces],
      {EdgeForm[{Dashed, Black}], FaceForm[Transparent], Polygon[FDrect.tau]}
    }] 
  ];


RGBColor[1., 0.4392156862745098, 0.4392156862745098, 1.]

End[]

EndPackage[]