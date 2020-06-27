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
PackageExport["RENull"]
PackageExport["RegexQ"]
PackageExport["CompoundRegexQ"]
PackageExport["RegexMatchQ"]
PackageExport["RegexNormal"]
PackageExport["RegexLength"]
PackageExport["REUnion"]
PackageExport["REConcat"]
PackageExport["REClosure"]
PackageExport["RegexSimplify"]
PackageExport["RegexFactor"]
PackageExport["RegexFullSimplify"]
PackageExport["RegexExpand"]
PackageExport["RandomRegex"]
PackageExport["RegexParse"]
PackageExport["ToRegex"]

PackageScope["regexLinearize"]
PackageScope["pSet"]
PackageScope["dSet"]
PackageScope["fSet"]

(* ::Section:: *)
(* Regex *)

(* ::Subsection:: *)
(* Clear Symbols *)
(*
Unprotect[EmptyString, RENull, REUnion, REConcat, REClosure];
ClearAll[
  EmptyString, RENull, RegexQ, CompoundRegexQ, RegexLength, REUnion, REConcat, REClosure, RegexSimplify, RegexFactor,
  RegexFullSimplify, RegexExpand, RegexParse, ToRegex, toRegexArray, reduceRegexArray, uwExpr, regexArrayEliminate,
  nextEliminationFunction, findEliminationGroups, bridgeStates, horizontalChop, adjacencyIntersection, arrangeFirstLast,
  findPath, $regexFactorizationRules, $regexSimplificationRules, $regexAdditionalSimplificationRules
];
*)

(* ::Subsection:: *)
(* Symbols *)

EmptyString::usage = "EmptyString is a symbol representing the string of length 0.";
ToString[EmptyString] ^= "";
Protect[EmptyString];


RENull::usage = "RENull is a symbol for the regular expression capturing the empty set, i.e., the expression that matches nothing.";
ToString[RENull] ^= "\[EmptySet]";
Protect[RENull];

(* ::Subsection:: *)
(* Properties *)
RegexQ::usage = "RegexQ[expr] yields True when expr is atomic, or has head REUnion, REConcat or REClosure.
RegexQ[expr, patt] gives True if expr is RENull or EmptyString, or is atomic and matches patt, or is a compound regex where every subexpression at level -1 that is not RENull or EmptyString matches patt.";
RegexQ[_REConcat | _REUnion | _REClosure | _?AtomQ] = True ;
RegexQ[_] = False;
RegexQ[r_, patt_] := MatchQ[r, patt] || CompoundRegexQ[r, patt];
RegexQ[_, _] = False;


CompoundRegexQ::usage = "CompoundRegexQ[expr] returs True if expr has head REUnion, REConcat, or REClosure.
CompoundRegexQ[expr, patt] returns True if expr is a compound regex where every subexpression at level -1 that is not RENull or EmptyString matches patt.";
CompoundRegexQ[_REConcat | _REUnion | _REClosure] = True;
CompoundRegexQ[_] = False;
CompoundRegexQ[r : (_REConcat | _REUnion | _REClosure), patt_] :=
    AllTrue[Level[r, {-1}], MatchQ[patt | RENull | EmptyString]];
CompoundRegexQ[_, _] = False;


RegexMatchQ::usage = "RegexMatchQ[regex, expr] returns True if expr is matched by regex.
RegexMatchQ[expr] represents an operator form of RegexMatchQ.";
RegexMatchQ[r_, EmptyString] := matchesEmptyQ[r];
RegexMatchQ[r_ /; RegexQ[r, _String], input_String] := StringMatchQ[input, RegexNormal@r];
RegexMatchQ[r_ /; RegexQ[r, _String], EmptyString] := StringMatchQ["", RegexNormal@r];
RegexMatchQ[r_ /; RegexQ[r, _String], _] = False;
RegexMatchQ[r_, input_] := ToNFA[r][input];
RegexMatchQ[input_][r_] := RegexMatchQ[r, input];


RegexNormal::usage = "RegexNormal[regex] converts the regex into an expression with head RegularExpression recognizing strings from the same language.";
RegexNormal[RENull] = RegularExpression["a^"];
RegexNormal[r_?RegexQ] := RegularExpression@ToString@Map[
  RightComposition[ToString,
    StringReplace[a : Characters[".$^?*+|{}()[]\\"] :> "\\" ~~ a],
    StringReplace[{s : (StartOfString ~~ _ | ("\\" ~~ _) ~~ EndOfString) :> s, s__ :> "(" ~~ s ~~ ")"}]],
  r, {-1}];


RegexLength::usage = "RegexLength[regex] gives the number of atomic subexpressions in regex. RegexLength is defined to be 0 in the special cases of RENull and EmptyString.";
SetAttributes[RegexLength, Listable];
RegexLength[R_?CompoundRegexQ] := Count[R, _, {-1}];
RegexLength[RENull | EmptyString] = 0;
RegexLength[_?AtomQ] = 1;

(* ::Subsection:: *)
(* Operators *)

(* ::Subsubsection:: *)
(* Union *)
REUnion::usage = "REUnion[e_1, e_2, ...] represents a regex matching the union e_1 | e_2 | ... of the expressions e_i.";
Default[REUnion] = RENull;
REUnion[x_.] := x;
SetAttributes[REUnion, Orderless];
REUnion[x_, x_ , a___] := REUnion @@ DeleteDuplicates[{x, a}];
REUnion[EmptyString, c_REClosure , a___] := REUnion[c, a];
SetAttributes[REUnion, {OneIdentity, Flat}];
REUnion[RENull, a_] := a;
REUnion[x_, REClosure[x_]] := REClosure[x];
REUnion /: ToString[u_REUnion] :=
    "(" <> StringRiffle[ToString /@ (List @@ u), "|"] <> ")";
Protect[REUnion];

(* ::Subsubsection:: *)
(* Concatenation *)
REConcat::usage = "REUnion[e_1, e_2, ...] represents a regex matching the concatenation e_1 e_2 ... of the expressions e_i.";
Default[REConcat] = EmptyString;
REConcat[___, RENull, ___] = RENull;
REConcat[x_.] := x;
REConcat[a___, EmptyString, b___] := REConcat[a, b];
SetAttributes[REConcat, {Flat, OneIdentity}];
REConcat /: ToString[c_REConcat] := StringRiffle[ToString /@ (List @@ c), ""];
Protect[REConcat];

(* ::Subsubsection:: *)
(* Closure *)
REClosure::usage = "REClosure[e] represents a regex matching the closure of expression e with respect to concatenation. This is defined as the set {EmptyString, e, ee, eee, ...}.";
REClosure[RENull | EmptyString] = EmptyString;
REClosure[REClosure[x_]] := REClosure[x];
REClosure /: MakeBoxes[REClosure[x_], form : (StandardForm | TraditionalForm)] := MakeBoxes[SuperStar@x, form];
REClosure /: ToString[REClosure[c_REConcat]] := "(" <> ToString[c] <> ")*";
REClosure /: ToString[c_REClosure] := ToString @@ c <> "*";
REClosure[_, x__] /; Message[REClosure::argx, REClosure, Length[{x}] + 1] = Null;
SyntaxInformation[REClosure] = {"ArgumentsPattern" -> {_}};
Protect[REClosure];

(* ::Subsection:: *)
(* Transformation *)

RegexSimplify::usage = "RegexSimplify[r] attempts to simplify the provided regular expression using simple pattern matching.";
RegexSimplify[r_, opts : OptionsPattern[ReplaceRepeated]] :=
    ReplaceRepeated[r, $regexSimplificationRules,
      filterOpts[{opts}, ReplaceRepeated]];


RegexFactor::usage = "RegexFactor[r] attempts to factor the given regular expression.";
RegexFactor[r_, opts : OptionsPattern[ReplaceRepeated]] :=
    ReplaceRepeated[r,
      $regexFactorizationRules,
      filterOpts[{opts}, ReplaceRepeated]];


RegexFullSimplify::usage = "RegexFullSimplify[r] applies additional techniques of factorization and regular language equivalence to simplify the given regular expression.";
Options[RegexFullSimplify] = {"Factorize" -> True};
RegexFullSimplify[r_, opts : OptionsPattern[{RegexFullSimplify, ReplaceRepeated}]] :=
    ReplaceRepeated[r, Dispatch[{
      $regexSimplificationRules,
      $regexAdditionalSimplificationRules,
      If[TrueQ[OptionValue["Factorize"]],
        $regexFactorizationRules, Nothing]}],
      filterOpts[{opts}, ReplaceRepeated]];


RegexExpand::usage = "RegexExpand[r] expands the given regular expression by distributing concatenation over unions.";
RegexExpand[c_REConcat] := If[FreeQ[c, _REUnion], c,
  Distribute[c, REUnion, REConcat, REUnion, RegexExpand /@ REConcat[##] &]];
RegexExpand[r_?CompoundRegexQ] := RegexExpand /@ r;
RegexExpand[a_] := a;

(* ::Subsection:: *)
(* Construction *)

RandomRegex::usage = "RandomRegex[n, k] returns a random regular expression on n symbols from an alphabet of length k.
RandomRegex[n,k,p] returns a random regular expression of n symbols from an alphabet of length k, where p is the probability of grouping.";
RandomRegex::probprm = "Parameter `1` at position `2` in `3` is expected to be a probability strictly less than 1.";
Options[RandomRegex] = {
  AlphabetFunction -> Automatic,
  EpsilonProbability -> 0
};
RandomRegex[n_Integer, alphin : (_List | _Integer), p : _?NumericQ : 0.5, OptionsPattern[]] :=
    With[{k = unless[alphin, _List, Length@alphin]},
      With[{alph = unless[alphin, _Integer, makeAlphabet[k, OptionValue["AlphabetFunction"]]]},
        Replace[
          NestWhile[
            Split[#, RandomChoice[{1 - p, p} -> {True, False}] &] &,
            ReplacePart[RandomChoice[alph, n],
              toAlternatives@RandomSample[1 ;; n,
                RandomVariate[BinomialDistribution[n, OptionValue[EpsilonProbability]]]] -> EmptyString
            ],
            Length[#] > 1 &,
            1, $IterationLimit, -1],
          {{a_} :> (RandomChoice[{REUnion, REConcat, REClosure}][a]),
            {a_, b__} :> (RandomChoice[{REUnion, REConcat}][a, b])},
          All]]
    ];


RegexParse::usage = "RegexParse[string] converts a regex in string form to an expression in terms of REUnion, REConcat, and REClosure. ";
RegexParse::parsererr = "Something happened at input `1` in `2`";
RegexParse::badexpect = "Was expecting `1`, but recieved `2`.";
Options[RegexParse] = {"ParseTree" -> False};
RegexParse[string_String, OptionsPattern[]] := With[{
  w = CreateDataStructure["Queue", Characters[string]]["Push", EndOfString],
  expr = With[{ops = If[OptionValue["ParseTree"], Inactive, Identity]
      /@ <|"|" -> REUnion, "." -> REConcat, "*" -> REClosure|>},
    (ops[#1][##2]) &],
  binaryQ = MatchQ["|"],
  postfixQ = MatchQ["*"],
  varQ = (StringQ[#] && StringMatchQ[#, RegularExpression["[^*()|\\\\]"]]) &,
  concatableQ = StringQ[#] && StringMatchQ[#, RegularExpression["[^*)|]"]] &,
  prec = <|"|" -> 0, "." -> 1, "*" -> 2|>,
  rprec = <|"|" -> 1, "." -> 2, "*" -> 2|>,
  nprec = <|"|" -> 0, "." -> 1, "*" -> 1|>},
  Module[{A, expectAfter, escape},
    expectAfter[return_, c_] := With[{d = w["Pop"]},
      If[MatchQ[d, c], return,
        Throw[Failure["SyntaxError",
          <|"MessageTemplate" -> "Expected `1` at position `2` but received `3`.",
            "MessageParameters" -> {c, StringLength[string] - w["Length"], d}|>]]
      ]];
    escape[c_] := With[{d = w["Pop"]},
      If[StringQ[d] &&
          StringMatchQ[d, RegularExpression["[*()|\\\\]"]], d,
        Throw[Failure["SyntaxError",
          <|"MessageTemplate" -> "Unrecognized escape sequence `1``2` at position `3`.",
            "MessageParameters" -> {c, d, StringLength[string] - w["Length"]}|>]]]];

    A[p_] := Module[{
      t = Switch[w["Peek"],
        "(", expectAfter[w["Pop"]; A[0], ")"],
        "\\", escape[w["Pop"]],
        _?varQ, w["Pop"],
        _, EmptyString],
      nxt = w["Peek"], r = 2, s},
      While[True,
        t = Which[
          binaryQ[nxt] && p <= prec[nxt] <= r, expr[s = w["Pop"], t, A[rprec[s]]],
          postfixQ[nxt] && p <= prec[nxt] <= r, expr[s = w["Pop"], t],
          concatableQ[nxt] && p <= prec["."] <= r,
          expr[s = ".", t, A[rprec[s]]], True, Break[]];
        {r, nxt} = {nprec[s], w["Peek"]}];
      t];
    (*Algorithm start*)
    Catch@expectAfter[A[0], EndOfString]]];


ToRegex::usage = "ToRegex[A] converts the automaton A to an equivalent regular expression.";
Options[ToRegex] = {Method -> Automatic};
ToRegex[A_?AutomatonQ, opts : OptionsPattern[reduceRegexArray]] :=
    reduceRegexArray[toRegexArray[A], filterOpts[{opts}, reduceRegexArray]];
ToRegex[r_?RegexQ, OptionsPattern[reduceRegexArray]] := r;

(* ::Subsection:: *)
(* Package Scope *)

regexLinearize::usage = "regexLinearize[regex] linearizes regex by indexing each character occurrence.
regexLinearize[regex, i] linearizes regex by indexing each character occurrence, starting at i.
regexLinearize[regex, i, True] returns a list {r, {a_1, a_2, ...}} where r is the linearization of regex, and the a_i are the symbols in the alphabet of r";
regexLinearize[r_, starti_Integer : 1, returnAlphabet_ : False] := Module[
  {i = starti,
    patt = Except[_REUnion | _REClosure | _REConcat | REUnion | REClosure | REConcat | EmptyString] },
  If[returnAlphabet,
    Reap[r /. p : patt :> Sow[Subscript[p, i++], "newalph"], "newalph", Sequence @@ ##2 &],
    r /. p : patt :> Subscript[p, i++]]
];


pSet::usage = "pSet[regex] returns the set of prefix characters of strings recognized by regex.";
pSet[RENull | EmptyString | Subscript[EmptyString, _] | PatternSequence[]] = {};
pSet[HoldPattern[REUnion[x__]]] := Catenate[pSet /@ {x}];
pSet[HoldPattern[REClosure[x_]]] := pSet[x];
pSet[HoldPattern[REConcat[
  Longest[x___?matchesEmptyQ],
  Longest[y : RepeatedNull[_, 1]],
  ___]]] := Catenate[{Catenate[pSet /@ {x}], pSet[y]}];
pSet[x_] := {x};

dSet::usage = "dSet[regex] returns the set of suffix characters of strings recognized by regex.";
dSet[RENull | EmptyString | Subscript[EmptyString, _], PatternSequence[]] = {};
dSet[HoldPattern[REUnion[x__]]] := Catenate[dSet /@ {x}];
dSet[HoldPattern[REClosure[x_]]] := dSet[x];
dSet[HoldPattern[REConcat[
  Shortest[___],
  RepeatedNull[x_, 1],
  Longest[y___?matchesEmptyQ]]]] := Catenate[{dSet[x], Catenate[dSet /@ {y}]}];
dSet[x_] := {x};

fSet::usage = "fSet[regex] returns the set of factors of length 2 in regex.";
fSet[HoldPattern[REUnion[x__]]] := Catenate[fSet /@ {x}];
fSet[HoldPattern[REClosure[x_]]] := Catenate[{fSet[x], Tuples[{dSet[x], pSet[x]}]}];
fSet[HoldPattern[REConcat[x_, y_]]] := Catenate[{fSet[x], fSet[y], Tuples[{dSet[x], pSet[y]}]}];
fSet[_] = {};

(* ::Subsection:: *)
(* Private Functions *)

(* Convert to expression NFA represented as a SparseArray adjacency matrix.
   initial and terminal state of eNFA at positions 1 and -1 respectively  *)
toRegexArray[A_?AutomatonQ] := With[{
  states = States[A], T = AutomatonType[A],
  inits = IDs[A, "Initial"], terms = IDs[A, "Terminal"],
  swap = Function[Null, {#1, #2} = {#2, #1}, HoldAll]},
  With[{addnewinit = Length@inits != 1,
    addnewterm = Length@terms != 1 || inits === terms}, (* init and term index must be distinct *)
    Module[{getidx,
      idxs = IDs[A, "Index"] + Boole[addnewinit],
      n = StateCount[A] + Boole[addnewinit] + Boole[addnewterm]},
      If[! addnewterm, (* If we're not adding a new terminal state *)
        swap[idxs[First@terms], idxs[[-1]]]]; (* Make the index of the old terminal state n *)
      If[! addnewinit, (* If we're not adding a new initial state *)
        If[idxs[[1]] == 1, (* True unless idx[[1]] got swapped with idx[[-1]] in previous step *)
          swap[idxs[First@inits], idxs[[1]]], (* Make the index of the old initial state 1 *)
          swap[idxs[First@inits], idxs[[-1]]]]]; (* Make the index of the old initial state idxs[[-1]] = 1 *)

      getidx[id_] :=
          With[{idx = (getidx[id] = idxs[id])},
            (KeyValueMap[Switch[T,
              NFA, Sow[#1, {idx, getidx[#]} & /@ #2] & ,
              DFA, Sow[#1, {{idx, getidx[#2]}}] &],
              Transitions[#]];
            If[InitialQ[#], Sow[EmptyString, {{1, idx}}]];
            If[TerminalQ[#], Sow[EmptyString, {{idx, n}}]];
            ) &@states[id];
            idx];

      SparseArray[
        DeleteCases[
          Last@Reap[Scan[getidx, inits], _, Rule[#1, REUnion @@ #2] &],
          HoldPattern[{x_, x_} -> EmptyString]], (* Delete any \[CurlyEpsilon] self-transitions *)
        n, RENull]]]
];


Options[reduceRegexArray] = {Method -> Automatic, "SimplificationFunction" -> Automatic};
reduceRegexArray::badorder = "Method \"SpecificOrder\" must be specified as {\"SpecificOrder\", perm}, where perm \
  is a valid permutation of ``, and n is the length of the given array.";
reduceRegexArray[regexArray_?SquareMatrixQ, OptionsPattern[]] := Module[{
  arr = regexArray,
  simp = unless[OptionValue["SimplificationFunction"],
    Automatic, RegexSimplify, None, Identity]},
  With[{idxs = Range[2, Length@arr - 1],
    reduce = regexArrayEliminate[arr, simp],
    method = validatedMethod[OptionValue[Method], {Automatic, "Shortest", "LeastCommon", "MostCommon",
      "ForwardOrder", "ReverseOrder", "RandomOrder", "SpecificOrder"}, reduceRegexArray] },
    Switch[method,
      "ForwardOrder", Scan[reduce, idxs],
      "ReverseOrder", Scan[reduce, Reverse@idxs],
      "RandomOrder", Scan[reduce, RandomSample[idxs]],
      "SpecificOrder", With[{ perm = Last[OptionValue[Method], Message[reduceRegexArray::badorder, idxs]; idxs]},
      If[Sort@perm === idxs, Scan[reduce, perm],
        Message[reduceRegexArray::badorder, idxs]; Scan[reduce, idxs]]],
      _, With[{next = nextEliminationFunction[arr, method, Break[]]},
      While[True, reduce@next[]]]];
    reduce[0]]
];


matchesEmptyQ[EmptyString | _REClosure] = True;
matchesEmptyQ[HoldPattern[REUnion[x__]]] := AnyTrue[{x}, matchesEmptyQ];
matchesEmptyQ[HoldPattern[REConcat[x__]]] := AllTrue[{x}, matchesEmptyQ];
matchesEmptyQ[_] = False;


uwExpr[uw_, uv_, vv_, vw_] := REUnion[uw, REConcat[uv, REClosure[vv], vw]];
SetAttributes[regexArrayEliminate, HoldFirst];
regexArrayEliminate[arr_, simp_][0] := (* recover final expression from reduced array *)
    simp@REConcat[
      REClosure@simp@uwExpr[arr[[1, 1]], arr[[1, -1]], arr[[-1, -1]], arr[[-1, 1]]],
      arr[[1, -1]],
      REClosure@simp@uwExpr[arr[[-1, -1]], arr[[-1, 1]], arr[[1, 1]], arr[[1, -1]]]];
regexArrayEliminate[arr_, simp_][v_] := With[
  {vv = arr[[v, v]]},
  arr[[v, v]] = RENull;
  Outer[(arr[[##]] = simp@uwExpr[arr[[##]], arr[[#1, v]], vv, arr[[v, #2]]]) &,
    Flatten@arr[[All, v]]["NonzeroPositions"],
    Flatten@arr[[v]]["NonzeroPositions"]];
  arr[[v, All]] = arr[[All, v]] = RENull;
];


SetAttributes[nextEliminationFunction, HoldAll];
nextEliminationFunction[arr_, method_, default_] := With[
  {nonzeroVals = Function[ Join[arr[[#]], Delete[arr[[All, #]], #]]["NonzeroValues"]]},
  With[{nextf = Switch[method,
    Automatic | "Shortest", First@*MinimalBy[Total@*RegexLength@*nonzeroVals],
    "MostCommon", First@*MaximalBy[Length@*nonzeroVals],
    "LeastCommon", First@*MinimalBy[Length@*nonzeroVals]]},
    Module[{groups = CreateDataStructure["Queue",
      Switch[method,
        Automatic, findEliminationGroups[arr],
        _, {Range[2, Length@arr - 1]}]],
      indices = {}},
      (If[Length[indices] == 0 && ! groups["EmptyQ"],
        indices = groups["Pop"]];
      If[Length[indices] == 0, default,
        (indices = DeleteCases[indices, #]; #) &@ nextf[indices]]) &]]
];


findEliminationGroups[arr_SparseArray, s_ : 1, t_ : Automatic, subset_ : All] :=
    findEliminationGroups[arr, s, autoAlt[t, Length@arr], unless[subset, All, rangeOver@arr]];
findEliminationGroups[arr_SparseArray, s_, t_, subset_] := Module[
  {div, lvl},
  lvl[l_][x_] := (lvl[_][x] = l);

  div[l_][ss : {_, _}] := Scan[lvl[l], ss];
  div[l_][ss : {u_, v__, w_}] := (
    Scan[lvl[l], {u, w}];
    With[{bridges = bridgeStates[arr, u, w, ss]},
      Switch[Length@bridges,
        Length@{v}, Scan[lvl[l + 1], {v}],
        _?Positive,
        BlockMap[ (* For each pair of sequential bridge states *)
          Function[{pair},
            Scan[div[l + 1], (* recursively apply div to subautomata *)
              horizontalChop[arr, Sequence @@ pair, ss]]],
          Flatten@{u, bridges, w}, 2, 1],
        _, Null]]);

  div[0][arrangeFirstLast[subset, s, t]];
  ReverseSortBy[GatherBy[
    DeleteCases[subset, s | t],
    lvl[Infinity]], lvl[Infinity]@*First]
];


bridgeStates[arr_SparseArray, s_ : 1, t_ : Automatic, subset_ : All] :=
    bridgeStates[arr, s, autoAlt[t, Length@arr], subset];
bridgeStates[arr_SparseArray, s_, t_, subset_] := With[{
  adjlists = adjacencyIntersection[arr, subset],
  path = findPath[arr, s, t, subset],
  anc = CreateDataStructure["FixedArray", Length@arr],
  min = CreateDataStructure["FixedArray", Length@arr],
  max = CreateDataStructure["FixedArray", Length@arr]},
  If[Length@path == 0, {}, (* s and t disconnected *)
    Module[{dfs, onPath, setMinMax, notbridges},
      onPath[toAlternatives@path] = True; onPath[_] = False;

      notbridges = Function[{v},
        Flatten[Range @@@ {
          {min["Part", v] + 1, anc["Part", v]},
          {anc["Part", v] + 1, max["Part", v] - 1}}], Listable];

      setMinMax[v_, {}] :=
          min["Part", v] = max["Part", v] = anc["Part", v];
      setMinMax[v_, succVals_] :=
          MapThread[(#1["Part", v] =
              First[#2[#3, UpTo[1]], anc["Part", v]]) &,
            {{min, max}, {TakeSmallest, TakeLargest}, Transpose@succVals}];

      dfs[prev_ : 0][v_] := (dfs[_][v] = Null;
      With[{succs = adjlists[[v]],
        p = First[If[onPath@v, FirstPosition[path, v]], 0]},
        Scan[dfs[anc["Part", v] = Max[p, prev]],
          If[0 < p < Length@path,
            rotateToFront[succs, path[[p + 1]]],
            succs]];
        setMinMax[v,
          If[onPath@#,
            ConstantArray[anc["Part", #], 2],
            Through[{min, max}["Part", #]]] &
              /@ succs]]);

      dfs[]@s;
      Delete[path, Transpose@List@Flatten@{1, -1, notbridges@path}]]]
];


horizontalChop[arr_SparseArray, s_ : 1, t_ : Automatic, subset_ : All] :=
    horizontalChop[arr, s, autoAlt[t, Length@arr], subset];
horizontalChop[arr_SparseArray, s_, t_, subset_] := With[
  {groups = CreateDataStructure["DisjointSet"],
    adjlists = adjacencyIntersection[arr, subset]},
  Module[{assign},
    assign[v_] := (
      assign[v] = v;
      groups["Insert", v];
      Scan[If[# =!= t, groups["Unify", v, assign[#]]] &,
        adjlists[[v]]];
      v );

    Scan[assign, DeleteCases[adjlists[[s]], s | t]];
    If[groups["EmptyQ"], {{s, t}}, arrangeFirstLast[#, s, t] & /@ groups["Subsets"]]]
];


adjacencyIntersection[arr_SparseArray, subset_] :=
    If[subset === All, arr["AdjacencyLists"],
      Intersection[subset, #] & /@ arr["AdjacencyLists"]];


arrangeFirstLast[l_List, first_, last_] :=
    {first, Splice@DeleteDuplicates[l, first | last], last};
arrangeFirstLast[expr_, first_, last_] :=
    expr /. h_[ p : OrderlessPatternSequence[Except[first | last] ...]] :> h[first, p, last];


findPath[arr_SparseArray, s_ : 1, t_ : Automatic, subset_ : All] :=
    findPath[arr, s, autoAlt[t, Length@arr], subset];
findPath[arr_SparseArray, s_, t_, subset_] := With[
  {neighbors = adjacencyIntersection[arr, subset]},
  Module[{dfs},
    dfs[v_] := (dfs[v] = Null;
    Catch[If[MemberQ[neighbors[[v]], t],
      Throw[Sow[t], "path"],
      Scan[dfs, neighbors[[v]]]],
      "path", Throw[{v, #1}, #2] &]);
    Block[{$RecursionLimit = Max[(Length@arr)^2 + 1, $RecursionLimit]},
      unless[Catch[dfs[s], "path", Flatten[#1] &],
        Null, {}]]]
];


$regexFactorizationRules = Dispatch[{
  HoldPattern[u : REUnion[x_, REConcat[x_, r_]]] :>
      REConcat[x, REUnion[r, EmptyString]],
  HoldPattern[u : REUnion[x_, REConcat[r_, x_]]] :>
      REConcat[REUnion[r, EmptyString], x],
  HoldPattern[u : REUnion[Repeated[
    REConcat[prefix_., Shortest[_.], suffix_.] /; !SameQ[prefix, suffix, EmptyString],
    {2, Infinity}]]
  ] :> REConcat[prefix, Replace[u, REConcat[prefix, x_., suffix] :> x, {1}], suffix]
}];


$regexSimplificationRules = Dispatch[{
  HoldPattern[REConcat[c : REClosure[REConcat[(x_) ..] | x_], x_]
  ] :> REConcat[x, c], (*  x*x \[Rule] xx* and [xx...]*x -> x[ xx...]*  (standard form)  *)
  HoldPattern[REConcat[REClosure[x_], x_, REClosure[x_]]
  ] :> REConcat[x, REClosure[x]], (*  x*xx* -> xx*  *)
  HoldPattern[REConcat[c_REClosure ..]
  ] :> c, (*  x*x* -> x*  *)
  HoldPattern[REClosure[REUnion[EmptyString, x_]]
  ] :> REClosure[x], (* [\[CurlyEpsilon]|x]* -> x* *)
  HoldPattern[ REUnion[x_ | REClosure[x_], c : REClosure[REUnion[x_ | REClosure[x_], _.]] , a_.]
  ] :> REUnion[c, a], (*  x|[x|y]* -> [x|y]*  *)
  HoldPattern[REUnion[EmptyString, REConcat[x_, REClosure[x_]]]
  ] :> REClosure[x], (*  \[CurlyEpsilon]|xx* -> x*  (this one seems to happen a lot converting FAs to regex *)
  HoldPattern[REClosure[REUnion[x_, REConcat[(x_) ..], a_.]]
  ] :> REClosure[REUnion[x, a]], (*  [x|[xx...]]* -> x* *)
  HoldPattern[ REClosure[REUnion[c : REConcat[x__], REConcat[(x__) ..], a_.]]
  ] :> REClosure[REUnion[c, a]], (*  [xy|[xyxy...]]* -> [xy]*  *)
  HoldPattern[REClosure[u : REUnion[__REClosure, _]]
  ] :> REClosure[Replace[u, REClosure[a_] :> a, {1}]], (*  [x| y*]* -> [x|y]*  *)
  HoldPattern[REClosure[c : REConcat[__REClosure]]
  ] :> REClosure[REUnion @@ Sequence @@@ c] (*  [x*y*]* -> [x| y]*  *)
}];


$regexAdditionalSimplificationRules = Dispatch[{
  HoldPattern[REUnion[x_, y_] /; SubsetLanguageQ[x, y]] :> y ,
  HoldPattern[ REConcat[x_REClosure, y_REClosure] /; SubsetLanguageQ[x, y]] :> y,
  HoldPattern[(REConcat[x_, y_REClosure] | REConcat[y_REClosure, x_]) /; SubsetLanguageQ[x, y]] :> y
}];
