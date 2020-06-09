(* Mathematica Init file *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

Block[{Notation`AutoLoadNotationPalette = False},
  Get[FileNameJoin[{ParentDirectory[DirectoryName@$InputFileName], "Automata.m"}]];
  Needs["Notation`"];
  With[{infix = Notation`InfixNotation, pbw = Notation`ParsedBoxWrapper,
    notation = Notation`Notation@*DoubleLongLeftRightArrow, alias = Notation`AddInputAlias},
    infix[pbw[TagBox["\[VerticalSeparator\]", Identity, SyntaxForm -> "+"]], Automata`RegexUnion];
    infix[pbw[TagBox["\[InvisibleSpace\]", Identity, SyntaxForm -> "*"]], Automata`RegexConcat];
    notation[
      pbw[OverscriptBox["a_", "\[LeftArrow]"]],
      pbw[RowBox[List["Automata`AutomatonReversal", "[", "a_", "]"]]]];
    alias["ar" -> pbw[OverscriptBox["\[SelectionPlaceholder]", "\[LeftArrow]"]]];
    alias["ru" -> pbw[TagBox["\[VerticalSeparator]", Identity, SyntaxForm -> "+"]]];
    alias["r " -> pbw[TagBox["\[InvisibleSpace\]", Identity, SyntaxForm -> "*"]]];
  ]
]



