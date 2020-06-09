(* Wolfram Language Package *)
(* Created by the Wolfram Language Plugin for IntelliJ, see http://wlplugin.halirutan.de/ *)

(* :Title: Regex *)
(* :Context: Regex` *)
(* :Author: kvlox *)
(* :Date: 2020-05-19 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 12.1 *)
(* :Copyright: (c) 2020 kvlox *)
(* :Keywords: *)
(* :Discussion: *)

Package["Automata`"]

PackageExport["EmptyString"]
PackageExport["RegexNull"]
PackageExport["RegexQ"]
PackageExport["RegexLength"]
PackageExport["RegexUnion"]
PackageExport["RegexConcat"]
PackageExport["RegexClosure"]
PackageExport["RandomRegex"]
PackageExport["ParseRegex"]
PackageExport["ToRegex"]

(* ::Section:: *)
(* Symbols *)
EmptyString::usage = "EmptyString is a symbol representing the string of length 0.";
EmptyString /: MakeBoxes[EmptyString, StandardForm] := InterpretationBox[
  StyleBox["\[CurlyEpsilon]", FontColor -> GrayLevel[0.5]], EmptyString];
EmptyString /: MakeBoxes[EmptyString, TraditionalForm] := InterpretationBox["\[CurlyEpsilon]", EmptyString];
ToString[EmptyString] ^= "";
Protect[EmptyString];

RegexNull::usage = "RegexNull is a symbol for the regular expression capturing the empty set, i.e., the expression that matches nothing.";
RegexNull /: MakeBoxes[RegexNull, StandardForm | TraditionalForm] := InterpretationBox["\[EmptySet]", RegexNull];
ToString[RegexNull] ^= "\[EmptySet]";
Protect[RegexNull];

(* ::Section:: *)
(* Properties *)
RegexQ::usage = "RegexQ[expr] yields True when expr is RegexNull, or has head RegexUnion, RegexConcat or RegexClosure.";
RegexQ[_RegexConcat | _RegexUnion | _RegexClosure | RegexNull] = True ;
RegexQ[_] = False;

RegexLength::usage = "RegexLength[regex] gives the number of atomic subexpressions in regex.";
RegexLength[R_?RegexQ] := Count[R, _, {-1}];

(* ::Section:: *)
(* Operators *)

(* ::Subsection:: *)
(* Union *)
RegexUnion::usage = "RegexUnion[e_1, e_2, ...] represents a regex matching the union e_1 | e_2 | ... of the expressions e_i.";
Default[RegexUnion] = EmptyString;
RegexUnion[] = EmptyString;
RegexUnion[x_] := x;
SetAttributes[RegexUnion, Orderless];
RegexUnion[RegexNull, a___] := RegexUnion[a];
RegexUnion[x_, x_ , a___] := RegexUnion @@ DeleteDuplicates[{x, a}];
RegexUnion[x_, RegexClosure[x_] , a___] := RegexUnion[RegexClosure[x], a];
SetAttributes[RegexUnion, {OneIdentity, Flat}];
RegexUnion /: Factor[u : HoldPattern[RegexUnion[RegexConcat[prefix_, Shortest[_.]] ..]]] :=
    RegexConcat[prefix, Factor@Replace[u, RegexConcat[prefix, x_.] :> RegexConcat[x], {1}]];
RegexUnion /: Factor[u : HoldPattern[RegexUnion[RegexConcat[Shortest[_.], suffix_] ..]]] :=
    RegexConcat[ Factor@Replace[u, RegexConcat[x_., suffix] :> RegexConcat[x], {1}], suffix];
RegexUnion /: Factor[u_RegexUnion] := u;
RegexUnion /: ToString[u_RegexUnion] := "(" <> StringRiffle[ToString /@ (List @@ u), "|"] <> ")";
Protect[RegexUnion];

(* ::Subsection:: *)
(* Concatenation *)
RegexConcat::usage = "RegexUnion[e_1, e_2, ...] represents a regex matching the concatenation e_1 e_2 ... of the expressions e_i.";
Default[RegexConcat] = EmptyString;
RegexConcat[] = EmptyString;
RegexConcat[x_] := x;
SetAttributes[RegexConcat, {Flat, OneIdentity}];
RegexConcat[___, RegexNull, ___] := RegexNull;
RegexConcat[a___, EmptyString, b___] := RegexConcat[a, b];
RegexConcat /: Expand[c_RegexConcat] := Distribute[c, RegexUnion, RegexConcat];
RegexConcat /: ExpandAll[c_RegexConcat?(FreeQ[RegexUnion])] := c;
RegexConcat /: ExpandAll[c_RegexConcat] :=
    Distribute[c, RegexUnion, RegexConcat, RegexUnion, ExpandAll@RegexConcat[##] &];
RegexConcat /: ToString[c_RegexConcat] := StringRiffle[ToString /@ (List @@ c), ""];
Protect[RegexConcat];

(* ::Subsection:: *)
(* Closure *)
RegexClosure::usage = "RegexClosure[e] represents a regex matching the closure of expression e with respect to concatenation. This is defined as the set {EmptyString, e, ee, eee, ...}.";
RegexClosure[] = EmptyString;
RegexClosure[RegexNull] = EmptyString;
RegexClosure[EmptyString] = EmptyString;
RegexClosure[RegexClosure[x_]] := RegexClosure[x];
RegexClosure[ a : Repeated[_, {2, Infinity}] /; Message[RegexClosure::argx, RegexClosure, Length[{a}]]] = RegexNull;
RegexClosure /: ToString[c : RegexClosure[_RegexConcat]] := "(" <> ToString @@ c <> ")*";
RegexClosure /: ToString[c_RegexClosure] := ToString @@ c <> "*";
RegexClosure /: MakeBoxes[s : RegexClosure[x_],
  form : (StandardForm | TraditionalForm)] :=
    TemplateBox[{MakeBoxes@SuperStar[x]},
      "RegexClosure",
      DisplayFunction -> (# &),
      InterpretationFunction -> (RowBox[{"RegexClosure", "[", #[[1]],
        "]"}] &)
    ];
SyntaxInformation[RegexClosure] = {"ArgumentsPattern" -> {_.}};
Protect[RegexClosure];

(* ::Section:: *)
(* Construction *)

RandomRegex::usage = "RandomRegex[n, k] returns a random regular expression on n symbols from an alphabet of length k.
RandomRegex[n,k,p] returns a random regular expression of n symbols from an alphabet of length k, where p is the probability of grouping.";
RandomRegex::probprm = "Parameter `1` at position `2` in `3` is expected to be a probability strictly less than 1.";
Options[RandomRegex] = {
  "Alphabet" -> Automatic,
  "AlphabetFunction" -> Automatic};
RandomRegex[n_, k_, p_ : 0.5, OptionsPattern[]] :=
    With[{alph = makeAlphabet[k, OptionValue["Alphabet"], OptionValue["AlphabetFunction"]]},
      Replace[
        NestWhile[
          Split[#, RandomChoice[{1 - p, p} -> {True, False}] &] &,
          RandomChoice[1 ;; k, n],
          Length[#] > 1 &,
          1, $IterationLimit, -1],
        {{a_} :> (RandomChoice[{RegexUnion, RegexConcat, RegexClosure}][ a]),
          {a_, b__} :> (RandomChoice[{RegexUnion, RegexConcat}][a, b])},
        All] /. AssociationThread[Range[k], alph]];

ParseRegex::usage = "ParseRegex[string] converts a regex in string form to an expression in terms of RegexUnion, \
RegexConcat, and RegexClosure. ";
ParseRegex::parsererr = "Something happened at input `1` in `2`";
ParseRegex::badexpect = "Was expecting `1`, but recieved `2`.";
Options[ParseRegex] = {"ParseTree" -> False};
ParseRegex[string_String, OptionsPattern[]] :=
    With[{
      w = CreateDataStructure["Queue", Characters[string]]["Push", EndOfString],
      expr = With[{ops = If[OptionValue["ParseTree"], Inactive, Identity]
          /@ <|"|" -> RegexUnion, "~" -> RegexConcat, "*" -> RegexClosure|>},
        (ops[#1][##2]) &],
      binaryQ = MatchQ["|" | "~"],
      postfixQ = MatchQ["*"],
      varQ = (StringQ[#] && StringMatchQ[#, RegularExpression["[^*()|~]"]]) &,
      prec = <|"|" -> 0, "~" -> 1, "*" -> 2|>,
      rprec = <|"|" -> 1, "~" -> 2, "*" -> 2|>,
      nprec = <|"|" -> 0, "~" -> 1, "*" -> 1|>},
      Module[{A, expectAfter},
        expectAfter[return_, c_] := With[{d = w["Pop"]},
          If[MatchQ[d, c], return,
            Throw[Failure["SyntaxError",
              <| "MessageTemplate" -> "Expected `1` at position `2` but received `3`.",
                "MessageParameters" -> {c, StringLength[string] - w["Length"], d}|>]]]];
        A[p_] := Module[{
          t = Switch[w["Peek"],
            "(", expectAfter[w["Pop"]; A[0], ")"], _?varQ, w["Pop"] ,
            _, EmptyString], nxt = w["Peek"], r = 2, s},
          While[True,
            t = Which[
              binaryQ[nxt] && p <= prec[nxt] <= r, expr[s = w["Pop"], t, A[rprec[s]]],
              postfixQ[nxt] && p <= prec[nxt] <= r, expr[s = w["Pop"], t],
              (varQ[nxt] || MatchQ[nxt, "("]) && p <= prec["~"] <= r, expr[s = "~", t, A[rprec[s]]],
              True, Break[]];
            {r, nxt} = {nprec[s], w["Peek"]}];
          t];
        (* Algorithm start *)
        Catch@expectAfter[A[0], EndOfString]]];

ToRegex::usage = "ToRegex[A] converts the automaton A to an equivalent regular expression.";
Options[ToRegex] = {Method -> Automatic};
ToRegex[R_?RegexQ] := R;
ToRegex[A_?AutomatonQ, opts : OptionsPattern[reduceRegexArray]] :=
    reduceRegexArray[toRegexArray[A], filterOpts[{opts}, reduceRegexArray]];

reductionCandidateRankingFunction[method_] := With[{
  newEdgeCounts = (Length /@ #["AdjacencyLists"] *
      Length /@ Transpose[#]["AdjacencyLists"]) &},
  Switch[method,
    "MostCommon",
    Commonest@DeleteCases[Flatten@#["NonzeroPositions"], 1 | 2] &,
    "LeastCommon", With[{newn = newEdgeCounts[#]},
    FirstPosition[newn, Min[newn /. {0 -> Infinity}], {}]] &,
    "LeastCommonShortest" | Automatic, Function[{arr},
    With[{newn = newEdgeCounts[arr]},
      SortBy[Flatten@Position[newn, Min[newn /. {0 -> Infinity}]],
        LeafCount[
          Through[{arr[[#]], arr[[All, #]]}["NonzeroValues"]] &]]]]
  ]];

toRegexArray[A_?AutomatonQ] := SparseArray[
  Last@Reap[
    With[{newid = First /@ PositionIndex[IDs[A]] + 2},
      Scan[With[{id = newid[StateID[#]]},
        KeyValueMap[
          Switch[AutomatonType[A],
            NFA, Sow[#1, {id, newid[#]} & /@ #2] & ,
            DFA, Sow[#1, {{id, newid[#2]}}] &],
          Transitions@#]] &,
        States@A];
      Sow[EmptyString, Thread[{1, newid /@ IDs[A, "Initial"]}]];
      Sow[EmptyString, Thread[{newid /@ IDs[A, "Terminal"], 2}]]],
    _, Rule[#1, RegexUnion @@ #2] &], Length@IDs[A] + 2, RegexNull];

Options[reduceRegexArray] = {Method -> Automatic, "SimplifyIntermediates" -> True};
reduceRegexArray[regexArray_?SquareMatrixQ, OptionsPattern[]] :=
    Module[{reduce, arr = regexArray,
      simp =
          If[TrueQ@OptionValue["SimplifyIntermediates"], Factor, Identity],
      method = validatedMethod[OptionValue[Method],
        {Automatic, "LeastCommonShortest", "LeastCommon", "MostCommon",
          "ForwardOrder", "ReverseOrder", "RandomOrder"},
        reduceRegexArray]},
      reduce[q_] := With[{q2q = RegexClosure[arr[[q, q]]]},
        arr[[q, q]] = RegexNull;
        Outer[(arr[[##]] = simp@RegexUnion[
          arr[[##]], RegexConcat[arr[[#1, q]], q2q, arr[[q, #2]]]]) &,
          Flatten@arr[[All, q]]["NonzeroPositions"],
          Flatten@arr[[q]]["NonzeroPositions"]];
        arr[[q, All]] = arr[[All, q]] = RegexNull;];
      Switch[method,
        "ForwardOrder", Scan[reduce, Range[3, Length@arr]],
        "ReverseOrder", Scan[reduce, Range[Length@arr, 3, -1]],
        "RandomOrder", Scan[reduce, RandomSample@Range[3, Length@arr]],
        _, With[{rank = reductionCandidateRankingFunction[method]},
        While[True, reduce@First[rank@arr, Break[]]]]];
      arr[[1, 2]]];

