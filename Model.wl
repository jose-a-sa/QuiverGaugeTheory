(* ::Package:: *)

BeginPackage["QuiverGaugeTheory`Model`", {
  "QuiverGaugeTheory`Tools`",
  "QuiverGaugeTheory`Core`",
  "QuiverGaugeTheory`Quiver`",
  "QuiverGaugeTheory`Moduli`",
  "QuiverGaugeTheory`Polytope`",
  "QuiverGaugeTheory`Perturbations`",
  "QuiverGaugeTheory`ExpandableBox`"
}]


Model::usage = "";
W::usage = "";
Quiver::usage = "";
ToricDiagram::usage = "";


Begin["`Private`"]


phaseKeyQ = MatchQ[{_String, _String}];


EmptyModel = Dataset[<|
  "Key" -> Missing["KeyAbsent", "Key"],
  "Descriptions" -> Missing["KeyAbsent", "Descriptions"],
  "Phases" -> Missing["KeyAbsent", "Phases"],
  "Potential" -> Missing["KeyAbsent", "Potential"],
  "ToricPotentialQ" -> Missing["KeyAbsent", "ToricPotentialQ"],
  "ToricDiagram" -> Missing["KeyAbsent", "ToricDiagram"],
  "Quiver" -> Missing["KeyAbsent", "Quiver"],
  "RCharges" -> Missing["KeyAbsent", "RCharges"],
  "Generators" -> Missing["KeyAbsent", "Generators"]
|>];


GetPhaseData[data_Dataset, phaseKey_String] := 
  Query[
    {"Key" -> Replace[x_ :> {x, phaseKey}]}
  ]@Query[
    {"Phases" -> Replace[ x_ -> Missing["KeyAbsent", "Phases"] ]},
    If[MissingQ@Query[phaseKey]@#, #, Query[phaseKey]@#] &
  ]@data;


GetModelData[key : (_String | {_String, _String}), old_Association, 
    opts_Association] :=
  Module[{modelDataPhasesRow, new, handlePhase, modelDataRow, modelDataRowList},
    handlePhase[pFlag_] := If[
      pFlag && phaseKeyQ@key,
      <|Last@key -> #|> &,
      Identity
    ];
    modelDataRow[n_String, k_String, g_:Identity, pFlag_:False] := If[
      KeyExistsQ[k]@opts,
      n -> handlePhase[pFlag]@g@Lookup[k]@opts,
      Nothing
    ];
    modelDataRowList[n_String, k_String, gList : {Rule[_String, _]..},
      pFlag_:False] := If[
        KeyExistsQ[k]@opts,
        n -> handlePhase[pFlag]@Association@DeleteCases[
          (#1 -> #2[Lookup[k]@opts] &) @@@ gList, _ -> (_?MissingQ)],
        Nothing
      ];
    modelDataPhasesRow = If[
      phaseKeyQ@key,
      "Phases" -> (If[ListQ@#, Union[#, {Last@key}], {Last@key}] &)@
        Lookup["Phases"]@old,
      Nothing
    ];
    new = <|
      "Key" -> First@Flatten[{key}],
      modelDataRow["Descriptions", "Descriptions"],
      modelDataPhasesRow,
      modelDataRow["Potential", "Potential", Expand, True],
      modelDataRow["ToricPotentialQ", "Potential", ToricPotentialQ, True],
      modelDataRowList["ToricDiagram", "ToricDiagram", {
        "Graphics" -> PolytopePlot,
        "Coordinates" -> Identity}, True],
      modelDataRowList["Quiver", "Potential", {
        "Edges" -> QuiverFromFields,
        "Graph" -> (QuiverGraph[Lookup[opts,"QuiverPositioning"], #] &),
        "Positioning" -> (Lookup[opts,"QuiverPositioning"] &)}, True],
      modelDataRow["RCharges", "RCharges"],
      modelDataRow["Generators", "Generators", Identity, True]
    |>;
    Merge[{old, new},
      If[Length[#] == 1 || MissingQ@Last@#, 
        First@#, 
        If[AllTrue[ #, MatchQ[<|(_String -> _)..|>] ],
          KeySort@Append[First@#, Last@#], Last@#] 
      ] &
    ]
  ];


Model[key : (_String | {_String, _String})] := Missing["Undefined", key] /;
  MissingQ@Query["Key"]@Model[key, "ModelData"]
Model[key : (_String | {_String, _String}), 
  q : PatternSequence[Except["ModelData"|_Rule|_RuleDelayed]..] ] := 
    Query[q]@Model[key, "ModelData"] //
      Switch[#, _Failure | _Missing, #, _, Normal@#] &;
Model[key : (_String | {_String, _String}), 
  opts : OptionsPattern[] /; UnsameQ[{opts}, {}] ] :=
    Module[{current, modelKey, phaseKey, parsedOpts},
      parsedOpts = Append[<|"QuiverPositioning"->Automatic|>, <|opts|>];
      modelKey = First@Flatten[{key}];
      current = Normal@If[
        Head@Model[modelKey, "ModelData"] =!= Dataset,
        EmptyModel, 
        Model[modelKey, "ModelData"]
      ];
      If[phaseKeyQ[key],
        phaseKey = Last@Flatten[{key}]; 
        Model[modelKey, "ModelData"] =
          Dataset@GetModelData[{modelKey, phaseKey}, current, parsedOpts];
        Model[{modelKey, phaseKey}, "ModelData"] =
          GetPhaseData[Model[modelKey, "ModelData"], phaseKey],
        Model[modelKey, "ModelData"] =
          Dataset@GetModelData[modelKey, current, parsedOpts]
      ];
      Model[key]
    ];


QueryWithPhase[k : (_String | {_String, _String}), {q1__}, {q2___}, f_:Identity] :=
  Module[{pList, r1}, 
    pList = Flatten@DeleteMissing@{Model[First@Flatten@{k}, "Phases"]};
    r1 = Model[k, q1];
    If[MissingQ@r1, Return@r1];
    If[!AssociationQ[r1], Return[f@r1] ];
    If[AnyTrue[pList, KeyExistsQ[r1, #] &], 
      Map[f]@Query[All, q2]@r1, 
      f@Query[q2]@r1
    ]
  ];


Model /: MakeBoxes[q : Model[key : (_String | {_String, _String})],
  fmt: (StandardForm|TraditionalForm)] :=
    Module[{header, grid, scaleDownGraphics, scaledDownGraph, 
        diagramBox, quiverBox, toricQBox, noFieldsBox, sizeB},
      scaleDownGraphics = ReplaceAll[{
        g_Graphics :> Graphics[First@g, 
            ImageSize -> UpTo[90] 
          ]
      }];
      sizeB = If[ MissingQ@Model[key, "Phases"], 500, 
        425 + 75*Length@Model[key, "Phases"] ];
      scaledDownGraph = QuiverGraph[Lookup[#, "Positioning"], Lookup[#, "Edges"], 
        ImageSize -> UpTo[130], 
        "ArrowSize" -> 0.07, 
        VertexSize -> {"Scaled", 0.07},
        VertexLabelStyle -> Directive[Bold, 10]
      ] &;
      diagramBox = ExpandableBoxItem[{"ToricDiagram: ", 
        QueryWithPhase[key, {"ToricDiagram"}, {"Graphics"}, scaleDownGraphics]}];
      quiverBox = ExpandableBoxItem[{"Quiver: ", 
        QueryWithPhase[key, {"Quiver"}, {{"Edges", "Positioning"}}, scaledDownGraph]}];
      toricQBox = ExpandableBoxItem[{"ToricPotentialQ: ", 
          QueryWithPhase[key, {"ToricPotentialQ"}, {}]}];
      noFieldsBox = ExpandableBoxItem[{"No. Fields: ", 
          QueryWithPhase[key, {"Potential"}, {}, Length@*Fields]}];
      header = StringRiffle[Flatten@{key}, " "];
      grid = ReplaceAll[{Repeated[SpanFromLeft, 5]} -> Nothing]@{
        {ExpandableBoxItem[{"Key: ", key}],
        ExpandableBoxItem[{"Descriptions: ", Model[key, "Descriptions"]}],
        ExpandableBoxItem[{"Phases: ", Model[key, "Phases"]}]},
        {ExpandableBoxItem[{"Potential: ", 
          QueryWithPhase[key, {"Potential"}, {}]}, ImageSize -> UpTo[sizeB] ], 
        SpanFromLeft, SpanFromLeft},
        Sequence @@ If[ MissingQ@Model[key, "Phases"], 
          {{toricQBox, noFieldsBox, SpanFromLeft}}, 
          {{toricQBox, SpanFromLeft, SpanFromLeft},
           {noFieldsBox, SpanFromLeft, SpanFromLeft}}
        ],
        Sequence @@ If[ MissingQ@Model[key, "Phases"], 
          {{diagramBox, quiverBox, SpanFromLeft}}, 
          {{diagramBox, SpanFromLeft, SpanFromLeft},
           {quiverBox, SpanFromLeft, SpanFromLeft}}
        ]
      };
      ExpandableBox[q, header, grid, fmt]
    ];


W[ Model[key : (_String | {_String, _String})] ] :=
  Model[key, "Potential"];


Quiver[ Model[key : (_String | {_String, _String})] ] :=
  QueryWithPhase[key, {"Quiver"}, {"Edges"}];


QuiverFields[ Model[key : (_String | {_String, _String})] ] :=
  QueryWithPhase[key, {"Potential"}, {}, Fields];


QuiverFields[ Model[key : (_String | {_String, _String})] ] :=
  QueryWithPhase[key, {"Quiver"}, {"Graph"}];


QuiverGraph[ Model[key : (_String | {_String, _String})] ] :=
  QueryWithPhase[key, {"Quiver"}, {"Graph"}];
QuiverGraph[Model[key : (_String | {_String, _String})], opts: OptionsPattern[Graph] ] := 
  QueryWithPhase[key, {"Quiver"}, {"Edges"}, (QuiverGraph[Automatic, #, opts]&)];
QuiverGraph[vertex:{(_Integer|{__Integer})..}, 
  Model[key : (_String | {_String, _String})], opts: OptionsPattern[Graph] ] :=
    QueryWithPhase[key, {"Quiver"}, {"Edges"}, (QuiverGraph[vertex, #, opts]&)];


ToricDiagram[ Model[key : (_String | {_String, _String})], opts: OptionsPattern[Graphics] ] :=
  QueryWithPhase[key, {"ToricDiagram"}, {"Coordinates"}, (PolytopePlot[#, opts]&)];


GeneratorsTable[ Model[key : (_String | {_String, _String})] ] :=
  Module[{genTableF},
    genTableF = GeneratorsTable[
      Query["Potential"]@#, 
      Query["Generators"]@#,
      Model[key, "RCharges"] ] &;
    If[MissingQ@Model[key, "Phases"],
      genTableF,
      Map[genTableF]@*Transpose
    ]@Model[key, {"Potential", "Generators"}]
  ];


End[]

 
EndPackage[]