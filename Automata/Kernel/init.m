(* Mathematica Init file *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

Block[{Notation`AutoLoadNotationPalette = False},
  Get[FileNameJoin[{ParentDirectory[DirectoryName@$InputFileName], "Automata.m"}]];
  Needs["Notation`"];
  With[{style = StyleBox[#, FontWeight -> Bold, FontColor -> GrayLevel[0.5]] &,
    noEdit = Sequence @@ {Editable -> False, Selectable -> False},
    pbw = Notation`ParsedBoxWrapper, infix = Notation`InfixNotation,
    alias = Notation`AddInputAlias, note = Notation`Notation},
    With[{unionOp = pbw[TagBox[style["|"],
      Identity, noEdit, SyntaxForm -> "+"]],
      concatOp = pbw[TagBox[style["\[RoundSpaceIndicator\]"],
        Identity, noEdit, SyntaxForm -> "*"]],
      esSym =
          pbw[TagBox[style["\[CurlyEpsilon\]"], Automata`EmptyString, noEdit]],
      nullSym = pbw[TagBox[style["\[EmptySet\]"], Automata`RENull, noEdit]]},
      infix[unionOp, Automata`REUnion];
      infix[concatOp, Automata`REConcat];
      note[DoubleLongLeftRightArrow[esSym, pbw["EmptyString"]]];
      note[DoubleLongLeftRightArrow[nullSym, pbw["RENull"]]];
      note[DoubleLongRightArrow[
        pbw[SuperscriptBox["a_", "*"]],
        pbw[RowBox[{"REClosure", "[", "a_", "]"}]]]];
      note[DoubleLongLeftRightArrow[
        pbw[OverscriptBox["a_", "\[LeftArrow]"]],
        pbw[RowBox[{"Automata`AutomatonReversal", "[", "a_", "]"}]]]];
      alias["r " -> concatOp];
      alias["ru" -> unionOp];
      alias["re" -> esSym];
      alias["rn" -> nullSym];
      alias["ar" -> pbw[OverscriptBox["\[SelectionPlaceholder]", "\[LeftArrow]"]]];
    ]
  ]


  (*
  With[{infix = Notation`InfixNotation, pbw = Notation`ParsedBoxWrapper,
    notation = Notation`Notation@*DoubleLongLeftRightArrow, alias = Notation`AddInputAlias},
    infix[pbw[TagBox["\[VerticalSeparator\]", Identity, SyntaxForm -> "+"]], Automata`RegexUnion];
    infix[pbw[TagBox["\[InvisibleSpace\]", Identity, SyntaxForm -> "*"]], Automata`RegexConcat];
    alias["reu" -> pbw[TagBox["\[VerticalSeparator]", Identity, SyntaxForm -> "+"]]];
    alias["reg" -> pbw[TagBox["\[InvisibleSpace\]", Identity, SyntaxForm -> "*"]]];
  ]
*)
]

