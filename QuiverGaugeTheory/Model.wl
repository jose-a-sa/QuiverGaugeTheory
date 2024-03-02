(* ::Package:: *)

Unprotect["QuiverGaugeTheory`Model`*"];
ClearAll["QuiverGaugeTheory`Model`*"];


BeginPackage["QuiverGaugeTheory`Model`", {
  "QuiverGaugeTheory`Utils`",
  "QuiverGaugeTheory`Core`",
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Tiling`",
  "QuiverGaugeTheory`Moduli`",
  "QuiverGaugeTheory`Polytope`",
  "QuiverGaugeTheory`Perturbations`",
  "QuiverGaugeTheory`ExpandableBox`"
}]


ModelKeyQ::usage = "";
ModelKeyExistsQ::usage = "";
ModelQ::usage = "";
Model::usage = "";
ClearModel::usage = "";
ClearAllModels::usage = "";
W::usage = "";
Quiver::usage = "";


Begin["`Private`"]


ModelKeyQ[_String | {_String, _String}] := True;
ModelKeyQ[_] := False;
SetAttributes[ModelKeyQ, {Protected, ReadProtected}];


ModelKeyExistsQ[k_?ModelKeyQ] := 
  AssociationQ@ModelData[k];
ModelKeyExistsQ[_] := False;
SetAttributes[ModelKeyExistsQ, {Protected, ReadProtected}];


ModelData[q : HoldPattern[Model][key_?ModelKeyQ] ] := ModelData[key];
If[!MatchQ[ModelData[], _List],
  ModelData[] = {}
];
SetAttributes[ModelData, {HoldFirst}];


ClearModel[ HoldPattern[Model][key_?ModelKeyQ] ] := 
  ClearModel[key]
ClearModel[key_?ModelKeyQ] :=
  Module[{},
    ModelData[] = DeleteCases[ModelData[], HoldPattern[Model][key] ];
  ];
SetAttributes[ClearModel, {HoldFirst, Protected, ReadProtected}];


ClearAllModels[] := 
  Module[{},
    Clear[ModelData];
    SetAttributes[ModelData, {HoldFirst}];
    ModelData[q : HoldPattern[Model][key_?ModelKeyQ] ] := ModelData[key];
    ModelData[] = {};
  ];
SetAttributes[ClearAllModels, {HoldFirst, Protected, ReadProtected}];


updateModelDataList[ key_?ModelKeyQ  ] :=
  Module[{old},
    old = If[ListQ@ModelData[],
      DeleteCases[ModelData[], HoldPattern[Model][key] ],
      {}
    ];
    ModelData[] = Join[old, {Model[key]}];
    Model[key]
  ];


handlePotential[W_?PotentialQ, qPos : ({(_Integer|{__Integer})..}|Automatic) : Automatic] :=
  Module[{quiver, new, td, tdPlot, P, fieldsPM, newToric},
    quiver = QuiverFromFields[W];
    new = {
      "Potential" -> W,
      "ToricPotentialQ" -> ToricPotentialQ[W],
      "Quiver" -> quiver,
      "QuiverGraph" -> QuiverGraph[qPos, quiver],
      "QuiverPositioning" -> qPos
    };
    newToric = If[ToricPotentialQ@W,
      td = ToricDiagram[W];
      tdPlot = PolytopePlot[td];
      P = PerfectMatchingMatrix[W];
      fieldsPM = Map[
        (Times @@ Power[Keys@td, #] &),
        AssociationThread[FieldCases@W, P]
      ];
      {
        "ToricDiagram" -> td,
        "ToricDiagramGraph" -> tdPlot,
        "PerfectMatchings" -> Keys[td],
        "FieldPMDecomposition" -> fieldsPM
      },
      {}
    ];
    Association@Join[new, newToric]
  ];


handleGenerators[data_Association] :=
  Module[{pot, rchPM, rchF, pmDecomp, mes, redMes, gen},
    pot = data["Potential"];
    rchPM = Last@AMaximization[ data["ToricDiagram"] ];
    pmDecomp = data["FieldPMDecomposition"];
    rchF = Map[
      RootReduce@*ReplaceAll[KeyMap[Log]@rchPM]@*PowerExpand@*Log,
      pmDecomp
    ];
    latt = GeneratorsLattice[pot];
    mes = GaugeInvariantMesons[data["Quiver"], Infinity];
    redMes = DeleteCases[
      ReduceGenerators[pot, Join @@ Values@latt, ToGeneratorVariableRules@mes],
      HoldPattern[Rule][_, _Times | _Power]
    ];
    gen = GroupBy[Keys@redMes, ReplaceAll@pmDecomp];
    lattPM = Map[First]@GroupBy[
      ReplaceAll[pmDecomp]@Normal@latt,
      First@*Last -> First];
    Association[
      "ChiralMesons" -> redMes,
      "MesonicGenerators" -> gen,
      "RCharges" -> AppendTo[rchPM, rchF],
      "GeneratorsLattice" -> lattPM
    ]
  ];


Options[Model] = {
  "Descriptions" -> Missing["KeyAbsent", "Descriptions"],
  "LaTeXDescriptions" -> Missing["KeyAbsent", "LaTeXDescriptions"],
  "Potential" -> Missing["KeyAbsent", "Potential"],
  "QuiverPositioning" -> Automatic
};
Model[] := 
  ModelData[];
Model[key_?ModelKeyQ] :=
  Missing["Undefined", key] /; Not@ModelKeyExistsQ[key];
Model[key_?ModelKeyQ, k_String ] := 
  If[ ModelKeyExistsQ[key],
    Lookup[k]@ModelData[key],
    Missing["Undefined", key]
  ]
Model[key_?ModelKeyQ, "Properties"] := 
  If[ ModelKeyExistsQ[key],
    Keys@ModelData[key],
    Missing["Undefined", key]
  ]
Model[key_?ModelKeyQ, opts : OptionsPattern[Model] /; UnsameQ[{opts}, {}] ]  :=
  Module[{modelKey, new, q},
    modelKey = First@Flatten[{key}];
    new = Association[{
      "Key" -> modelKey,
      "Descriptions" -> OptionValue["Descriptions"],
      "LaTeXDescriptions" -> OptionValue["LaTeXDescriptions"]
    }];
    If[!PotentialQ@OptionValue["Potential"],
      Message[Model::mssgpot]; Return[Null]
    ];
    new = AssociateTo[new, 
      handlePotential[
        OptionValue["Potential"], 
        OptionValue["QuiverPositioning"]
      ]
    ];
    ModelData[key] = DeleteMissing[new];
    updateModelDataList[ key ]
  ];
Model::mssgpot = "Valid superpotential not specified.";


Model /: MakeBoxes[q : HoldPattern[Model][key_?ModelKeyExistsQ], fmt : (StandardForm | TraditionalForm)] := 
  Module[
    {data, handleBox, keyBox, descriptionsBox, potentialBox, 
      toricQBox, noFieldsBox, miniQuiver, quiverBox, scaleDownGraphics, 
      diagramBox, header, grid},
    data = ModelData[key];
    handleBox[l_, v_, f_ : Identity, opts : OptionsPattern[] ] :=
      If[MissingQ@v, SpanFromLeft, ExpandableBoxItem[{l, f@v}, opts] ];
    keyBox = ExpandableBoxItem[{"Key: ", key}];
    descriptionsBox = handleBox["Descriptions: ", Lookup["Descriptions"]@data];
    potentialBox = handleBox["Potential: ", Lookup["Potential"]@data, Identity,
      ImageSize -> UpTo[520] ];
    toricQBox = handleBox["ToricPotentialQ: ", Lookup["Potential"]@data, ToricPotentialQ];
    noFieldsBox = handleBox["No. FieldCases: ", Lookup["Potential"]@data, Length@*FieldCases];
    miniQuiver = QuiverGraph[
      Lookup["QuiverPositioning"]@data, Lookup["Quiver"]@data,
      ImageSize -> UpTo[130], 
      "ArrowSize" -> 0.07,
      VertexSize -> {"Scaled", 0.07},
      VertexLabelStyle -> Directive[Bold, 10]
    ] &;
    quiverBox = handleBox["Quiver: ", Lookup["QuiverGraph"]@data, miniQuiver];
    scaleDownGraphics = ReplaceAll[{g_Graphics :> Graphics[First@g, ImageSize -> UpTo[90] ]}];
    diagramBox = handleBox["ToricDiagram: ", Lookup["ToricDiagramGraph"]@data, scaleDownGraphics];
    header = StringRiffle[Flatten@{key}, " "];
    grid = ReplaceAll[{Repeated[SpanFromLeft, 5]} -> Nothing]@{
      {keyBox, descriptionsBox, SpanFromLeft},
      {potentialBox, SpanFromLeft, SpanFromLeft},
      {toricQBox, noFieldsBox, SpanFromLeft},
      {quiverBox, diagramBox, SpanFromLeft}};
    ExpandableBox[q, header, grid, fmt]
  ];


SetAttributes[Model, {Protected, ReadProtected}];


Unprotect[{W, Quiver, QuiverGraph, ToricDiagram, GeneratorsTable}];


W[ HoldPattern[Model][key_?ModelKeyQ] ] :=
  Model[key, "Potential"];


Quiver[ HoldPattern[Model][key_?ModelKeyQ] ] :=
  Model[key, "Quiver"];


QuiverGraph[ HoldPattern[Model][key_?ModelKeyQ], opts: OptionsPattern[QuiverGraph] ] := 
  Model[key, "QuiverGraph"];
QuiverGraph[ HoldPattern[Model][key_?ModelKeyQ], opts: OptionsPattern[QuiverGraph] ] :=
  QuiverGraph[Model[key, "QuiverPositioning"], Model[key, "Quiver"], opts];
QuiverGraph[vertex:{(_Integer|{__Integer})..}, Model[key_?ModelKeyQ], 
    opts: OptionsPattern[QuiverGraph] ] :=
  QuiverGraph[vertex, Model[key, "Quiver"], opts];


ToricDiagram[ HoldPattern[Model][key_?ModelKeyQ], m_?MatrixQ] :=
  Block[{mat},
    mat = If[Dimensions@m =!= {2,2} || PossibleZeroQ@Det@m, 
      IdentityMatrix[2], m];
    Map[ mat.# &, ToricDiagram[ Model[key] ] ]
  ];
ToricDiagram[ Model[key_?ModelKeyQ] ] :=
  Model[key, "ToricDiagram"]


GeneratorsTable[ HoldPattern[Model][key_?ModelKeyQ] ] :=
  Module[{data, pot},
    data = ModelData[key];
    pot = data["Potential"];
    If[! ToricPotentialQ@pot,
      Message[GeneratorsTable::nontoric]; Return[Null]
    ];
    If[!KeyExistsQ[data, "RCharges"],
      ModelData[key] = AppendTo[data,
        handleGenerators[data]
      ],
      Message[Abelianize::warn]
    ];
    GeneratorsTable[data]
  ];


Protect[{W, Quiver, QuiverGraph, ToricDiagram, GeneratorsTable}];


End[]

 
EndPackage[]