(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* RULES FOR MAX AND MIN *)


Unprotect[Min, Max];


(* Rules involving infinity. *)

Min[a_, Infinity] := a;

Max[a_, -Infinity] := a;

Min[a_, -Infinity] := -Infinity;

Max[a_, Infinity] := Infinity;


(* Rules for expressions with constant coefficients. *)

Max/: n_?Positive Max[a_, b_] := Max[Expand[n a], Expand[n b]];

Max/: n_?Negative Max[a_, b_] := Min[Expand[n a], Expand[n b]];

Min/: n_?Positive Min[a_, b_] := Min[Expand[n a], Expand[n b]];

Min/: n_?Negative Min[a_, b_] := Max[Expand[n a], Expand[n b]];


Max[0, 0] := 0;

Min[0, 0] := 0;


(* Simplification of expressions involving Max and Min. *)

Min[a_. + c_, b_. + c_] := Min[a, b] + c;

Max[a_. + c_, b_. + c_] := Max[a, b] + c;


Protect[Max,  Min];


(* Local rules for simplifying inequalities involving maximum or minimum. *)

MaxMinRules = {

(Min[a_, b_] < c_) :> or[a<c, b<c],

(Max[a_, b_] < c_) :> and[a<c, b<c],

(c_ < Min[a_, b_]) :> and[c<a, c<b],

(c_ < Max[a_, b_]) :> or[c<a, c<b],

(Min[a_, b_] <= c_) :> or[a<=c, b<=c],

(Max[a_, b_] <= c_) :> and[a<=c, b<=c],

(c_ <= Min[a_, b_]) :> and[c<=a, c<=b],

(c_ <= Max[a_, b_]) :> or[c<=a, c<=b]

};