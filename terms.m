(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* MANAGING THE LIST OF BASIC TERMS *)


(* Initialize the set of basic terms. *)

BasicTerms = {};

KnownUpper = {};

KnownLower = {};


(* Number of basic terms *)

NumberOfTerms := Length[BasicTerms];


(* IndexOf[l, e] stands for the index of element "e" in list "l". *)

IndexOf[{b___, a_, c___}, a_] := Length[{b}] + 1;

IndexOf[_, a_] := NewTerm[a];


(* TermNumber gives the index of a term in the basic term list. *)

TermNumber[a_] := IndexOf[BasicTerms, a];


(* Add a new term into the basic term list. *)

NewTerm[a_] := (
	AppendTo[BasicTerms, a];
	AppendTo[KnownUpper, Unknown];
	AppendTo[KnownLower, Unknown];
	NumberOfTerms);


(* Compute the number of different appearances of some
 pattern in the formula 'a'. *)

NumberOfAppearances[a_, pat_] :=
	Length[Appearances[a, pat]];

Appearances[a_, pat_] := 
	Union[Map[subexpressions[a], Position[a, pat]]];

subexpressions[f_][{a__}] := f[[a]];


(* get all variables in a formulas *)

VariablesIn[a_Const] := {a};

VariablesIn[a_Var] := {a};

(* VariablesIn[a_Symbol] := If[ConstantQ[a], {}, {a}]; *)

VariablesIn[a_Symbol] := {a};

VariablesIn[f_[a___]] := Apply[Union, Map[VariablesIn, {a}]];

VariablesIn[_] := {};


(* get a list of all basic terms in a formula *)

TermsIn[imp[a_, b_]] := Union[TermsIn[a], TermsIn[b]];

TermsIn[seq[a_, b_]] := Union[TermsIn[a], TermsIn[b]];

TermsIn[and[a_, b__]] := Apply[Union, Map[TermsIn, {a, b}]];

TermsIn[or[a_, b__]] := Apply[Union, Map[TermsIn, {a, b}]];

TermsIn[not[a_]] := TermsIn[a];

TermsIn[p_[a___]] := Apply[Union, Map[BasicTermsIn, {a}]];

TermsIn[_] := {};

BasicTermsIn[a_Const] := {a};

BasicTermsIn[a_Var] := {a};

BasicTermsIn[a_Symbol] := If[Defined[a], {}, {a}];

BasicTermsIn[f_[t_, {k_, index__}]] := 
	Complement[Apply[Union, Map[BasicTermsIn, {t, index}]], {k}]/;
	MemberQ[{sum, product, limit}, f];

BasicTermsIn[f_[a___]] := 
	If[Defined[f], Apply[Union, Map[BasicTermsIn, {a}]], {f[a]}];

BasicTermsIn[_] := {};

Defined[Pi] = True;

Defined[Plus] = True;

Defined[Times] = True;

Defined[Power] = True;

Defined[infinity] = True;

Defined[_] = False;