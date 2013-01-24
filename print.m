(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

Format[Ipart, TeXForm] := "I";

Format[Rpart, TeXForm] := "R";

Format[Ipart] := "I";

Format[Rpart] := "R";

Format[limit[f_, {a_, b_}], TeXForm] := 
	StringJoin["\\lim_{", ToString[TeXForm[a -> b]], "}\\left(", ToString[TeXForm[HoldForm[f]]], "\\right)"];

Format[f_all, TeXForm] :=
	StringJoin[PrintQuantifiers[f], "[", ToString[TeXForm[SkipQuantifiers[f]]], "]"];

Format[f_some, TeXForm] :=
	StringJoin[PrintQuantifiers[f], "[", ToString[TeXForm[SkipQuantifiers[f]]], "]"];

Format[seq[a_, b_]] := SequenceForm[HoldForm[a], " ===> ", HoldForm[b]];

Format[seq[a_, b_], TeXForm] := StringJoin[ToString[TeXForm[HoldForm[a]]], " \\Longrightarrow ", ToString[TeXForm[HoldForm[b]]]];

Format[imp[a_, b_]] := SequenceForm["(", HoldForm[a], " ==> ", HoldForm[b], ")"];

Format[imp[a_, b_], TeXForm] := 
	StringJoin["(", ToString[TeXForm[HoldForm[a]]], " \\Rightarrow ", ToString[TeXForm[HoldForm[b]]], ")"];

Unprotect[Sum];

Format[Sum[a_, {k_, low_, up_, cond_}], TeXForm] :=
	StringJoin["\\sum_{", ToString[TeXForm[HoldForm[LessEqual[low, k, up]]]], "}^{", ToString[TeXForm[cond]], "}", ToString[TeXForm[a]]];

Protect[Sum];

Format[Comma[a_, b__], TeXForm] :=
	StringJoin[ToString[TeXForm[HoldForm[a]]], ",", ToString[TeXForm[Comma[b]]]];

Format[Comma[a_], TeXForm] := a;

Unprotect[Abs];

Format[Abs[a_], TeXForm] := 
	StringJoin["\\left|", ToString[TeXForm[HoldForm[a]]], "\\right|"];

Protect[Abs];

Format[abbr[a_, b_]] := SequenceForm["(", HoldForm[b], " <=> ", HoldForm[a], ")"];

Format[abbr[a_, b_], TeXForm] := 
	StringJoin[ToString[TeXForm[HoldForm[b]]], " \\leftrightarrow ", ToString[TeXForm[HoldForm[a]]]];

Format[over[a_, b_]] := HoldForm[a/b];

Format[over[a_, b_], TeXForm] := HoldForm[a/b];

texform[Plus] := "+";

texform[Times] := " ";

texform[Or] := " \\vee ";

texform[And] := " \\wedge ";

texform[Comma] := " , ";



(* PRINTING. *)



(* Initialization for printing formulas in TeX Form. *)

outfile = "out.tex";
texfile = "out00.tex";

OpenWrite[outfile];

(* Set the TeXOn and SuccessStepsOnly flags on *)

SetPrint := (SuccessStepsOnly = True;);


WriteFiles[a__] := WriteToFile[outfile, a];

WriteFile1[a__] := WriteToFile[texfile, a];

WriteToFile[a__] := WriteString[a, "\n"];

StartProof := 
	(tempfile = ToString[Unique["out"]];
	texfile = StringJoin[tempfile, ".tex"];
	OpenWrite[texfile];
	WriteToFile[texfile, "\\documentstyle{cmu-art} \n\\parindent=0pt \n\\begin{document}"]; );

EndProof := 
	(
	PrintList[ProveHistory];
	ProveHistory = {};
	WriteFiles["\\framebox(10, 10){} \n"];
	Print["*** End Of Proof ***"];
	WriteToFile[outfile, "\\pagebreak\n"];
	WriteToFile[texfile, "\\end{document} \n"]; Close[texfile];
	Run["latex", texfile];
	Run["xdvi -s 3 ", tempfile, "&"];
	);

EndDocument := (
	SuccessStepsOnly = False;
	Close[outfile];
	outfile = "output.tex"; 
	OpenWrite[outfile];
	WriteToFile[outfile, "\\documentstyle{cmu-art} \n\\parindent=0pt \n\\begin{document}"]; 
	WriteToFile[outfile, "{\\bf Theorems proved :}"];
	PrintList[TheoremsProved];
	WriteToFile[outfile, "\\pagebreak \n\n"];
	Close[outfile];
	Run["cat out.tex >> output.tex"];
	outfile = "out.tex";
	OpenWrite[outfile];
	WriteToFile[outfile, "\\end{document} \n"]; Close[outfile];
	Run["cat out.tex >> output.tex"];
	Run["latex output"];
	Run["xdvi -s 3 output&"];
	outfile = "out.tex";
	OpenWrite[outfile];);

PrintBold[s_] :=
	(AppendTo[ProveHistory, bold[s]];
	WriteFiles["{\\bf ", s, "}"]; Print[]; Print[s]; Print[]);


(* Abbreviations for expressions. *)

Abbreviation = {};

SetAttributes[Abbreviate, HoldRest];

Abbreviate[f1_, f2_] := AppendTo[Abbreviation, f1 :> f2];

PrintAbbreviation[] := (
	PrintBold["Abbreviations used in proof:"];
	PrintAbbreviation[Abbreviation]);

Newpage[] := (
	PrintList[ProveHistory]; ProveHistory = {}; 
	WriteToFile[outfile, "\\pagebreak\n"];);

PrintAbbreviation[{}] := Null;

PrintAbbreviation[{f1_ :> f2_, b___}] := (
	PrintOut[abbr[f1 /. a_Pattern :> a[[1]] /. OperatorForm, HoldForm[f2]]];
	PrintAbbreviation[{b}]; );

PrintDefinition[] := (
	PrintBold["Definitions used in proof:"];
	PrintDefinition[UserFunctions];
	PrintList[ProveHistory]; ProveHistory = {};);

PrintDefinition[{}] := Null;

PrintDefinition[{f1_ :> f2_, b___}] := (
	PrintSequent[(f1 /. a_Pattern :> a[[1]]) == f2];
	PrintDefinition[{b}]);

PrintGiven[] := (
	PrintBold["Given properties:"];
	PrintGiven[GivenFormulas[]];
	PrintList[ProveHistory]; ProveHistory = {};);

PrintGiven[{}] := Null;

PrintGiven[{f1_, b___}] := (
	PrintSequent[f1];
	PrintGiven[{b}]);



(* Print the rule name. *)

print[a_, b__] := print[StringJoin[a, b]];

print[a_] := 
	(AppendTo[ProveHistory, a];
	 WriteFiles[a]; Print[]; Print[a]; Print[]);

print1[a_, b__] := print1[StringJoin[a, b]];

print1[a_] := 
	(WriteFiles[a]; Print[]; Print[a]; Print[]);


(* Print the output form of a formula. *)

Printform[f_] := 
	HoldForm[f] //. Abbreviation //. OperatorForm;

OperatorForm = 
	{and ->And, or -> Or, not[a_==b_] :> a!=b, not -> Not, 
	infinity -> Infinity, sum -> Sum, product -> Product, 
	complex[a_, Times[b_, c__]] :> a + Times[b, c, I],
	complex[a_, b_] :> a + b I};



(* Print the sequent to be proved. *)

PrintSequent[seq[True, c_]] := PrintSequent[c];

PrintSequent[c_] := PrintOut[Printform[Requantify[NegativePosition, c]]];

PrintLemma[c_] := PrintOut[Printform[Requantify[PositivePosition, c]]];

PrintOut[c_] := 
	(AppendTo[ProveHistory, c]; PrintFormula[c]);

PrintSequent1[seq[True, c_]] := PrintSequent1[c];

PrintSequent1[c_] := PrintFormula[Printform[Requantify[NegativePosition, c]]];


(* PrintMessage[message] prints out "message", which is generated
during simplification. *)

PrintMessage[{}] := Null;

PrintMessage[{{s_, f_}, rest___}] := 
	(PrintSequent[f]; print[s]; PrintMessage[{rest}]);



(* Print out the result. *)

PrintResult[rule_, result_] :=

	 (* Print the inference rule used. *)

 	(print[rule];

	 (* Print the result. *)

	 PrintOut[Printform[Requantify[1, result]]];

	 (* Print an empty line. *)

	 print[];

	 (* Return value. *)

	 result);



(* Set the current theorem label and print it. The label of a theorem
changes when the proof is split into two parts. If the previous label is
{a}, the labels for the two parts are {a, 1} and {a, 2}, respectively. *)

SetAndPrintLabel[l_] :=  print["case ", label = l, ":"];

SetAttributes[MultiLineForm, {HoldAll}];

MultiLineForm[f_] := ToString[TeXForm[HoldForm[f]]] /; !TooLong[f];

MultiLineForm[HoldForm[a_]] := MultiLineForm[a];

MultiLineForm[a_ / b_] := ToString[TeXForm[HoldForm[a / b]]] ;

MultiLineForm[seq[h_, c_]] := 
	StringJoin[MultiLineForm[h],
		"\\Longrightarrow \\\\ \n & &",
		MultiLineForm[c]];

MultiLineForm[imp[h_, c_]] := 
	StringJoin[MultiLineForm[h],
		"\\Rightarrow \\\\ \n & &",
		MultiLineForm[c]];

MultiLineForm[f_all] := 
	StringJoin[PrintQuantifiers[f], "[\\\\ \n & &",
		MultiLineForm[Release[SkipQuantifiers[f]]], "]"];

MultiLineForm[f_some] := 
	StringJoin[PrintQuantifiers[f], "[\\\\ \n & &",
		MultiLineForm[Release[SkipQuantifiers[f]]], "]"];

MultiLineForm[- a_] := StringJoin[" - (", MultiLineForm[a], ")"];

MultiLineForm[{a__}] := StringJoin[" \\{ ", MultiLineForm[Comma, a], " \\}"];

MultiLineForm[a_ == b_] := 
	StringJoin[MultiLineForm[a], "\\\\ \n & & = ", MultiLineForm[b]];

MultiLineForm[a_ <= b_] := 
	StringJoin[MultiLineForm[a], "\\\\ \n & & \\leq ", MultiLineForm[b]];

MultiLineForm[a_ < b_] := 
	StringJoin[MultiLineForm[a], "\\\\ \n & & < ", MultiLineForm[b]];

MultiLineForm[Plus[a_, b__]] :=
	MultiLineForm[Plus, a, b];

MultiLineForm[Times[a_, b__]] := 
	MultiLineForm[Times, a, b];

MultiLineForm[Or[a_, b__]] :=
	MultiLineForm[Or, a, b];

MultiLineForm[And[a_, b__]] :=
	MultiLineForm[And, a, b];

MultiLineForm[Sum[a_, {k_, min_, max_}]] :=
	StringJoin["\\sum_{", ToString[TeXForm[HoldForm[k]]], "=", ToString[TeXForm[min]], "}^{", ToString[TeXForm[HoldForm[max]]], "} (", MultiLineForm[a], ")"];

MultiLineForm[a_ -> b_] := 
	StringJoin[MultiLineForm[a], "\\rightarrow", MultiLineForm[b]];

MultiLineForm[f_[a__]] := StringJoin[ToString[TeXForm[f]], "(", MultiLineForm[Comma, a], ")"];

MultiLineForm[op_, a__, b_, c___] :=
	StringJoin[MultiLineForm[op, a], texform[op], " \\\\ \n & & ", MultiLineForm[op, b, c]] /; 
	TooLong[{a, b}] && (!TooLong[{a}] || Length[{a}] == 1);

MultiLineForm[And, a_Or] :=
	StringJoin["\\left(", ToString[TeXForm[HoldForm[a]]], "\\right)"];

MultiLineForm[op_, a_] :=
	ToString[TeXForm[HoldForm[a]]];

MultiLineForm[op_, a__] :=
	ToString[TeXForm[HoldForm[op[a]]]];

SetAttributes[TooLong, {HoldAll}];

TooLong[f_] := 
	Longest[0, Position[Append[Characters[ToString[HoldForm[f]]], "\n"],"\n"]] > 110 ;

Longest[n_, {rest___, n1_, n2_}] := 
	Longest[Max[n2-n1, n], {rest, n1}];

Longest[n_, {n1_}] := Max[n, n1];

PrintList[{a_, b___}] := (PrintFormula1[a]; PrintList[{b}]);

PrintList[{}] := Null;

PrintFormula1[bold[a_]] :=
	WriteFile1["{\\bf ", a, "}"]; 

PrintFormula1[a_String] := 
	WriteFile1[a]; 

PrintFormula1[c_] := 
	If[TooLong[c],
		WriteFile1["\\begin{eqnarray*}\n & &",
			MultiLineForm[c],
			"\n\\end{eqnarray*}"],
		WriteFile1["\\[ ", MultiLineForm[c], "\\]"]];

PrintFormula[bold[a_]] :=
	(WriteFiles["{\\bf ", a, "}"]; Print[a]);

PrintFormula[a_String] := 
	(WriteFiles[a]; Print[a]);

PrintFormula[c_] := (
	Print["   ", c];
	If[TooLong[c],
		WriteFiles["\\begin{eqnarray*}\n & &",
			MultiLineForm[c],
			"\n\\end{eqnarray*}"],
		WriteFiles["\\[ ", MultiLineForm[c], "\\]"]]);

SetAttributes[PrintQuantifiers, {HoldAll}];

SetAttributes[SkipQuantifiers, {HoldAll}];

PrintQuantifiers[all[x_, c_]] := 
	StringJoin["\\forall ", ToString[TeXForm[x]], PrintQuantifiers[c]];

PrintQuantifiers[some[x_, c_]] := 
	StringJoin["\\exists ", ToString[TeXForm[x]], PrintQuantifiers[c]];

PrintQuantifiers[c_] := "";

SkipQuantifiers[all[x_, c_]] := SkipQuantifiers[c];

SkipQuantifiers[some[x_, c_]] := SkipQuantifiers[c];

SkipQuantifiers[c_] := HoldForm[c];



(* SucceedWith[f] tries to retain only the success steps in the proof. *)

SetAttributes[SucceedWith, {HoldFirst}];

SucceedWith[f_] :=  (

	(* If not only print out success steps, just evaluate f *)

	(* otherwise, attach the print outs in evaluating "f" to the prove 
	history if it doesn't return false, through away the print outs
	when the return value if false *)

	Block[{u1, temph},
	 (temph = ProveHistory; ProveHistory = {};
	  If[FalseQ[u1 = f], 
		ProveHistory = temph,
		ProveHistory = Join[temph, ProveHistory]];
	  u1)]);

