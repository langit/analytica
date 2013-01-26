(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* RULES FOR LOGICAL OPERATORS *)



(* Rules for sequents *)


(* Conditions for truth of a sequent *)

seq[_, True] := True;

seq[False, _] := True;

seq[a_, a_] := True;

seq[And[a___, b_, c___], b_] := True;



(* Implication in the conclusion *)

seq[a_, imp[b_, c_]] := seq[And[b, a], c];

seq[a_, seq[b_, c_]] := seq[And[b, a], c];



(* Implication in the hypothesis *)

seq[imp[a_, b_], c_] := seq[Or[Not[a], b], c];

seq[And[h1___, imp[a_, b_], h2___], c_] := 
        seq[And[h1, Or[Not[a], b], h2], c];


seq[seq[a_, b_], c_] := seq[Or[Not[a], b], c];

seq[And[h1___, seq[a_, b_], h2___], c_] := 
        seq[And[h1, Or[Not[a], b], h2], c];



(* Negation of a sequent *)

Not[seq[a_, b_]] := And[a, Not[b]];



(* Additional operations on sequents *)

Or[a___, seq[h_, c_], b___] := seq[h, Or[a, c, b]];

imp[a_, seq[h_, c_]] := seq[And[a, h], c];



(* Negation in the hypothesis *)

seq[Not[a_], c_] := seq[True, Or[a, c]];

seq[And[h1___, Not[a_], h2___], c_] := seq[And[h1, h2], Or[a, c]];



(* Negation in the conclusion *)

seq[h_, Not[a_]] := seq[And[h, a], False];

seq[h_, Or[c1___, Not[a_], c2___]] := seq[And[h, a], Or[c1, c2]];



(* Simplification of logical formulas *)



(* Rules for "or" *)

Or[] := False;

Or[a___, NIL, b___] := Or[a, b];

Or[x_] := x;

Or[d___, Or[a_, b__], c___] := Or[d, a, b, c];

Or[d___, imp[a_, b_], c___] := imp[a, Or[d, b, c]];

Or[a___, False, b___] := Or[a, b];

Or[t1___, True, t2___] = True;

Or[a___, b_, c___, b_, d___] := Or[a, b, c, d];

Or[___, a_, ___, Not[a_], ___] = True;

Or[___, Not[a_], ___, a_, ___] = True;

Or[a___, b_, c___, And[___, b_, ___], d___] := Or[a, b, c, d];

Or[a___, And[___, b_, ___], c___, b_, d___] := Or[a, b, c, d];



(* Rules for "and" *)

And[] := True;

And[a___, NIL, b___] := And[a, b];

And[x_] := x;

And[d___, And[a_, b__], c___] := And[d, a, b, c];

And[a___, True, b___] := And[a, b];

And[t1___, False, t2___] = False;

And[a___, b_, c___, b_, d___] := And[a, b, c, d];

And[___, a_, ___, Not[a_], ___] = False;

And[___, Not[a_], ___, a_, ___] = False;

And[a___, b_, c___, Or[___, b_, ___], d___] := And[a, b, c, d];

And[a___, Or[___, b_, ___], c___, b_, d___] := And[a, b, c, d];



(* Rules for "implies" *)

imp[_, True] := True;

imp[False, _] := True;

imp[True, x_] := x;

imp[x_, False] := Not[x];

imp[x_, x_] := True;

imp[a_, imp[b_, c_]] := imp[And[a, b], c];



(* Rules for  "not" *)

Not[True] = False;

Not[False] = True;

Not[Not[a_]] := a;

Not[And[a_, b__]] := Or[Not[a],Not[And[b]]];

Not[Or[a_, b__]] := And[Not[a],Not[Or[b]]];

Not[imp[a_, b_]] := And[a, Not[b]];



(* Logical equivalence *)

eqv[a_, b_] = And[imp[a, b], imp[b, a]];



(* Conditional expressions *)

if[_, f_, f_] := f;

if[test_, f1_, f2_] :=   And[imp[test, f1],  imp[Not[test], f2]];



(* Local rules to convert Mathematica operators into our own *)

OperatorRules = {

Or -> or,

And -> and,

Not -> not

};



