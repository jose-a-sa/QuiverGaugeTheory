(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Model`", {
  "QuiverGaugeTheory`Tools`",
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
(*ModelData::usage = "";*)
W::usage = "";
Quiver::usage = "";


Begin["`Private`"]


ModelKeyQ[_String | {_String, _String}] := True;
ModelKeyQ[_] := False


ModelKeyExistsQ[k_?ModelKeyQ] := 
  AssociationQ@ModelData[k];
ModelKeyExistsQ[_] := False


SetAttributes[ModelData, {HoldFirst}]
ModelData[q : Model[key_?ModelKeyQ] ] := ModelData[key];
If[!MatchQ[ModelData[], _List],
  ModelData[] = {}
];


SetAttributes[ClearModel, {HoldFirst}]
ClearModel[ Model[key_?ModelKeyQ] ] := 
  ClearModel[key]
ClearModel[key_?ModelKeyQ] :=
  Module[{},
    ModelData[] = DeleteCases[ModelData[], Model[key] ];
  ]


ClearAllModels[] := 
  Module[{},
    Clear[ModelData];
    ModelData[q : Model[key_?ModelKeyQ] ] := ModelData[key];
    ModelData[] = {};
  ]


SetAttributes[updateModelDataList, {HoldFirst}]
updateModelDataList[q : Model[key_?ModelKeyQ] ] :=
  Module[{old},
    old = If[ListQ@ModelData[],
      DeleteCases[ModelData[], q],
      {}
    ];
    ModelData[] = Join[old, {q}];
    q
  ];


handlePotential[W_?PotentialQ, qPos : ({(_Integer|{__Integer})..}|Automatic) : Automatic] :=
  Module[{quiver, new, td, P, fieldsPM},
    quiver = QuiverFromFields[W];
    new = Association[{
      "Potential" -> W,
      "ToricPotentialQ" -> ToricPotentialQ[W],
      "Quiver" -> quiver,
      "QuiverGraph" -> QuiverGraph[qPos, quiver],
      "QuiverPositioning" -> qPos
    }];
    If[ToricPotentialQ@W,
      td = ToricDiagram[W];
      P = PerfectMatchingMatrix[W];
      fieldsPM = Map[
        (Times @@ Power[Keys@td, #] &),
        AssociationThread[Fields@W, P]
      ];
      new = AssociateTo[new, {
        "ToricDiagram" -> td,
        "ToricDiagramGraph" -> PolytopePlot[Values@td],
        "PerfectMatchings" -> Keys[td],
        "FieldPMDecomposition" -> fieldsPM
      }]
    ];
    Return@new
  ]


handleGenerators[data_Association] :=
  Module[{pot, rchPM, rchF, pmDecomp, mes, redMes, gen},
    pot = data["Potential"];
    rchPM = Last@AMaximization[ data["ToricDiagram"] ];
    pmDecomp = data["FieldPMDecomposition"];
    rchF = Map[
      RootReduce@*Total@*Select[NumericQ]@*ReplaceAll[rchPM]@*Apply[List],
      pmDecomp
    ];
    mes = GaugeInvariantMesons[data["Quiver"], Infinity];
    redMes = GroupBy[Last -> First]@DeleteCases[
      ReduceGenerators[pot, mes, Automatic],
      HoldPattern[Rule][_, _Times|_Power]
    ];
    gen = GroupBy[Join @@ Values@redMes, ReplaceAll@pmDecomp];
    Association[
      "ChiralMesons" -> redMes,
      "MesonicGenerators" -> gen,
      "RCharges" -> AppendTo[rchPM, rchF]
    ]
  ]


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
Model[key_?ModelKeyQ, opts : OptionsPattern[Model] ] :=
  Module[{modelKey, new},
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
    updateModelDataList[ Model[key] ]
  ] /; UnsameQ[{opts}, {}];
Model::mssgpot = "Valid superpotential not specified.";


Model /: MakeBoxes[q : Model[key_?ModelKeyExistsQ], fmt : (StandardForm | TraditionalForm)] := 
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
      ImageSize -> UpTo[500] ];
    toricQBox = handleBox["ToricPotentialQ: ", Lookup["Potential"]@data, ToricPotentialQ];
    noFieldsBox = handleBox["No. Fields: ", Lookup["Potential"]@data, Length@*Fields];
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


W[ Model[key_?ModelKeyQ] ] :=
  Model[key, "Potential"];


Quiver[ Model[key_?ModelKeyQ] ] :=
  Model[key, "Quiver"];


QuiverFields[ Model[key_?ModelKeyQ] ] :=
  Fields@Model[key, "Potential"];


QuiverGraph[ Model[key_?ModelKeyQ] ] := 
  Model[key, "QuiverGraph"];
QuiverGraph[ Model[key_?ModelKeyQ], opts: OptionsPattern[{QuiverGraph,Graph}] ] :=
  If[MissingQ@Model[key, "QuiverGraph"],
    Model[key, "QuiverGraph"],
    QuiverGraph[Model[key, "QuiverPositioning"], Model[key, "Quiver"], opts]
  ];
QuiverGraph[vertex:{(_Integer|{__Integer})..}, Model[key_?ModelKeyQ], 
  opts: OptionsPattern[{QuiverGraph,Graph}] ] :=
  If[MissingQ@Model[key, "QuiverGraph"],
    Model[key, "QuiverGraph"],
    QuiverGraph[vertex, Model[key, "Quiver"], opts]
  ];


ToricDiagram[ Model[key_?ModelKeyQ] ] :=
  Model[key, "ToricDiagram"]


GeneratorsTable[ Model[key_?ModelKeyQ] ] :=
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


End[]

 
EndPackage[]