(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)


(* RULES FOR INEQUALITIES. *)

InequalityRules = {



(* Standard form for inequalities. *)

(a_ != b_) :> not[a == b],

(a_ > b_) :>  (b < a), 

(a_ >= b_) :> (b <= a),

Less[a_, b_, c__] :> and[a<b, Less[b, c]],

Greater[a_, b_, c__] :> and[a>b, Greater[b, c]],

LessEqual[a_, b_, c__] :> and[a<=b, LessEqual[b, c]],

GreaterEqual[a_, b_, c__] :> and[a>=b, GreaterEqual[b, c]],



(* Rules involving relations between 0 and a product. *)

(x_ a_ < 0) :> or[and[0 < x, a < 0], and[0 < a, x < 0]], 

(x_ a_ <=  0) :> or[and[0 <= x, a <= 0], and[0 <= a, x <= 0]],

(0 < x_ a_) :> or[and[0 < x, 0 < a], and[a < 0, x < 0]],

(0 <= x_ a_) :> or[and[0 <= x, 0 <= a], and[a <= 0, x <= 0]],



(* Remove a common additive term from both sides. *)

(x_ <= y_) :> (x - y <= 0) /; x =!= 0 && y =!= 0,

(x_ < y_) :> (x - y < 0) /; x =!= 0 && y =!= 0,

(0 <= x_ + y_) :> (-x - y <= 0),

(0 < x_ + y_) :> (-x - y < 0),



(* Decide the sign of a power. *)

(0 <= a_^n_) :> True /; WeakSimplify[0<=a],

(0 < a_^n_) :> True /; WeakSimplify[0<a],

(a_^n_ <= 0) :> False /; WeakSimplify[0<a],

(a_^n_ < 0) :> False/; WeakSimplify[0<=a],

(0 < a_^n_?Negative) :> (0 < a ^ (-n)),

(0 <= a_^n_?Negative) :> (0 < a ^ (-n)),

(0 <= a_^n_) :> or[0<=a, Even[n]]/;integer[n],

(a_^n_ <= 0) :> or[a==0, and[a<0, not[Even[n]]]]/;integer[n],

(0 < a_^n_) :> or[0<a, and[a<0, Even[n]]]/;integer[n],

(a_^n_ < 0) :> and[a<0, not[Even[n]]]/;integer[n],



(* Use atomic subformula to simplify other parts of the formula.  The
conditions are used to insure that the rules derived from the
subformula are not complicated and can be applied to the other parts
of the formula. *)

or[a___, b_ < c_, d___] :> or[b<c, (or[a, d] /. RulesFrom[c<=b])] /;
	!TooComplicated[b<c] && appears[{a, d}, b-c],

or[a___, b_ <= c_, d___] :> or[b<=c, (or[a, d] /. RulesFrom[c<b])] /;
	!TooComplicated[b<=c] && appears[{a, d}, b-c],

or[a___, b_ == c_, d___] :> or[b==c, (or[a, d] /. RulesFrom[not[c==b]])] /;
	!TooComplicated[b == c] && appears[{a, d}, b-c],

and[a___, b_ < c_, d___] :> and[b<c, (and[a, d] /. RulesFrom[b<c])] /;
	!TooComplicated[b<c] && appears[{a, d}, b-c],

and[a___, b_ <= c_, d___] :> and[b<=c, (and[a, d] /. RulesFrom[b<=c])] /;
	!TooComplicated[b<=c] && appears[{a, d}, b-c],

and[a___, b_ == c_, d___] :> and[b==c, (and[a, d] /. RulesFrom[b==c])] /;
	!TooComplicated[b==c] && appears[{a, d}, b-c],


(* Rules to decide sign of a summation. *)

(0 <= sum[f_, range_]) :> True /; WeakSimplify[0<=f],

(sum[f_, range_] <= 0) :> True /; WeakSimplify[f<=0]

};


(* Decide if an expression is too complicated. *)

TooComplicated[a_] := LeafCount[a]>30;


(* appears[f, a] checks to see if f contains the subformulas
a<0, a==0, or a<=0 *)

appears[f_, a_] := 
	!FreeQ[f, _Less?(#[[1]] - #[[2]] + a === 0 || 
                         #[[2]] -#[[1]] + a === 0&)] ||
	!FreeQ[f, _Equal?(#[[1]] - #[[2]] + a === 0 || 
                          #[[2]] -#[[1]] + a === 0&)] ||
	!FreeQ[f, _LessEqual?(#[[1]] - #[[2]] + a === 0 || 
                            #[[2]] -#[[1]] + a === 0&)];




(* Global rules for the negation of inequalities. *)

not[a_ < b_] := (b <= a);

not[a_ <= b_] := (b < a);



(* Decide truth of equalities and inequalities by their bound values. *)

RulesForRelations = {

f1_ <= f2_ :> False /; (!TooComplicated[f1-f2] && IsPositive[Lower[f1-f2]]),

f1_ <= f2_ :> True /; (!TooComplicated[f1-f2] && NotNegative[Lower[f2-f1]]),

f1_ < f2_ :> False /; (!TooComplicated[f1-f2] && NotNegative[Lower[f1-f2]]),

f1_ < f2_ :> True /; (!TooComplicated[f1-f2] && IsPositive[Lower[f2-f1]]),

f1_ == f2_ :> False /; (!TooComplicated[f1-f2] && 
		(IsPositive[Lower[f1-f2]] || IsPositive[Lower[f2-f1]]))

};



(* Decide if a list contains a positive number. *)

IsPositive[{a_, b___}] := positive[a] || IsPositive[{b}];

IsPositive[{}] := False;



(* Decide if a list contains a non-positive number. *)

NotNegative[{a_, b___}] := nonnegative[a] || NotNegative[{b}];

NotNegative[{}] := False;



(* Rules for determining when a number is positive. *)

positive[Strict[a_]] := nonnegative[a];

positive[c_?NumberQ] := (c>0);

positive[a_ + b_] := 
	(positive[a] && nonnegative[b]) || (positive[b] && nonnegative[a]);

positive[_] = False;



(* Rules for determining when a number is non-negative. *)

nonnegative[Strict[a_]] := nonnegative[a];

nonnegative[a_ + b_] := nonnegative[a] && nonnegative[b];

nonnegative[a_ b_] := 
	(nonnegative[a] && nonnegative[b]) || (nonpositive[a] && nonpositive[b]);

nonnegative[c_?NumberQ] := (c>=0);

nonnegative[_Abs] := True;

nonnegative[a_ ^ b_] := (IntegerQ[b] && Even[b]) || nonnegative[a];

nonnegative[_] := False;

nonpositive[Strict[a_]] := nonpositive[a];

nonpositive[c_?NumberQ] := (c<=0);

nonpositive[a_ + b_] := nonpositive[a] && nonpositive[b];

nonpositive[a_ b_] := 
	nonpositive[a] && nonnegative[b] || nonpositive[b] && nonnegative[a];

nonpositive[_] := False;


