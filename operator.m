(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* RULES FOR LOGICAL OPERATORS *)



(* Rules for sequents *)


(* Conditions for truth of a sequent *)

seq[_, True] := True;

seq[False, _] := True;

seq[a_, a_] := True;

seq[and[a___, b_, c___], b_] := True;



(* Implication in the conclusion *)

seq[a_, imp[b_, c_]] := seq[and[b, a], c];

seq[a_, seq[b_, c_]] := seq[and[b, a], c];



(* Implication in the hypothesis *)

seq[imp[a_, b_], c_] := seq[or[not[a], b], c];

seq[and[h1___, imp[a_, b_], h2___], c_] := 
        seq[and[h1, or[not[a], b], h2], c];


seq[seq[a_, b_], c_] := seq[or[not[a], b], c];

seq[and[h1___, seq[a_, b_], h2___], c_] := 
        seq[and[h1, or[not[a], b], h2], c];



(* Negation of a sequent *)

not[seq[a_, b_]] := and[a, not[b]];



(* Additional operations on sequents *)

or[a___, seq[h_, c_], b___] := seq[h, or[a, c, b]];

imp[a_, seq[h_, c_]] := seq[and[a, h], c];



(* Negation in the hypothesis *)

seq[not[a_], c_] := seq[True, or[a, c]];

seq[and[h1___, not[a_], h2___], c_] := seq[and[h1, h2], or[a, c]];



(* Negation in the conclusion *)

seq[h_, not[a_]] := seq[and[h, a], False];

seq[h_, or[c1___, not[a_], c2___]] := seq[and[h, a], or[c1, c2]];



(* Simplification of logical formulas *)



(* Rules for "or" *)

or[] := False;

or[a___, NIL, b___] := or[a, b];

or[x_] := x;

or[d___, or[a_, b__], c___] := or[d, a, b, c];

or[d___, imp[a_, b_], c___] := imp[a, or[d, b, c]];

or[a___, False, b___] := or[a, b];

or[t1___, True, t2___] = True;

or[a___, b_, c___, b_, d___] := or[a, b, c, d];

or[___, a_, ___, not[a_], ___] = True;

or[___, not[a_], ___, a_, ___] = True;

or[a___, b_, c___, and[___, b_, ___], d___] := or[a, b, c, d];

or[a___, and[___, b_, ___], c___, b_, d___] := or[a, b, c, d];



(* Rules for "and" *)

and[] := True;

and[a___, NIL, b___] := and[a, b];

and[x_] := x;

and[d___, and[a_, b__], c___] := and[d, a, b, c];

and[a___, True, b___] := and[a, b];

and[t1___, False, t2___] = False;

and[a___, b_, c___, b_, d___] := and[a, b, c, d];

and[___, a_, ___, not[a_], ___] = False;

and[___, not[a_], ___, a_, ___] = False;

and[a___, b_, c___, or[___, b_, ___], d___] := and[a, b, c, d];

and[a___, or[___, b_, ___], c___, b_, d___] := and[a, b, c, d];



(* Rules for "implies" *)

imp[_, True] := True;

imp[False, _] := True;

imp[True, x_] := x;

imp[x_, False] := not[x];

imp[x_, x_] := True;

imp[a_, imp[b_, c_]] := imp[and[a, b], c];



(* Rules for  "not" *)

not[True] = False;

not[False] = True;

not[not[a_]] := a;

not[and[a_, b__]] := or[not[a],not[and[b]]];

not[or[a_, b__]] := and[not[a],not[or[b]]];

not[imp[a_, b_]] := and[a, not[b]];



(* Logical equivalence *)

eqv[a_, b_] = and[imp[a, b], imp[b, a]];



(* Conditional expressions *)

if[_, f_, f_] := f;

if[test_, f1_, f2_] :=   and[imp[test, f1],  imp[not[test], f2]];



(* Local rules to convert Mathematica operators into our own *)

OperatorRules = {

Or -> or,

And -> and,

Not -> not

};



