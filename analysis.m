(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* PROPERTIES OF CONTINUOUS FUNCTIONS. *)



integer[round[b_]] := True;



(* Continuous[f[x], {x, x0}] is True when f is continuous at point x0. *)

(* UniformlyContinuous[f] is True when f uniformly continuous on its range. *)

(* UniformlyConvergent[sum[f[x, k], {k, n, infinity}], {x, c1, c2}] means
   the summation converges uniformly on interval [c1, c2]. *)



(* The identity function is continuous everywhere. *)

Continuous[x_, {x_, _}] := True;



(* A constant function is continuous everywhere. *)

Continuous[a_, {x_, _}] := True/; IsConstant[a, x];



(* Addition and Multiplication are continuous. *)

ContinuousFunction[Plus] = True;

ContinuousFunction[Times] = True;



(* Monomials are continuous. *)

Continuous[a_ ^ n_?integer, {x_, x0_}] :=
	True /;
	IsConstant[n, x] && Continuous[a, {x, x0}] && WeakSimplify[or[a!=0, n>=0]];



(* A sum of continuous functions is continuous. *)

Continuous[sum[f_, {k_, n1_, n2_}], {x_, x0_}] :=
	True /;
	FreeQ[n1, infinity] && FreeQ[n2, infinity] && Continuous[f, {x, x0}];




(* The composition of two continuous functions is continuous. *)

Continuous[f_[a__], {x_, x0_}] := 
	Apply[and, Map[Continuous[#, {x, x0}] &, {a}]] /; 
	ContinuousFunction[f];



(* A continuous function whose domain is a closed set is uniformily 
continuous. *)

UniformlyContinuous[f_] := True /; 
	ContinuousFunction[f] && Closed[Domain[f]];



(* Decide if a term is constant with respect to a certain variable. *)

IsConstant[Pi, x_] := True;

IsConstant[Const[___], x_] := True;

IsConstant[f_, x_] := False /; !FreeQ[f, x];

IsConstant[f_[a___], x_] := 
	Apply[and, Map[IsConstant[#, x]&, {a}]] /; f=!=Var;

IsConstant[_?NumberQ, x_] := True;



(* Decide if a function is monotonic. *)

Increasing[delta[f_]] := True;

Increasing[inverse[f_]] := Increasing[f];

Decreasing[inverse[f_]] := Decreasing[f];

Increasing[_] := False;

Decreasing[_] := False;



(* Decide if a function is bounded. *)

Bounded[f_] := True /; ContinuousFunction[f] && Closed[Domain[f]];



(* Decide if a set is closed. *)

Closed[ClosedInterval[a_, b_]] := True;



(* Properties of inverse functions. *)

inverse /: f_[inverse[f_][x_]] := x;

inverse[f_][f_[x_]] := x;



(* Delta is from the epsilon - delta argument about the continuity of 
   function, written as delta[f][epsilon]. *)

delta /: (0 < delta[_][_]) := True;

delta /: (0 <= delta[_][_]) := True;

delta /: (delta[_][_] < 0) := False;

delta /: (delta[_][_] <= 0) := False;

inverse /: (0 < inverse[delta[_]][_]) := True;

inverse /: (0 <= inverse[delta[_]][_]) := True;

inverse /: (inverse[delta[_]][_] < 0) := False;

inverse /: (inverse[delta[_]][_] <= 0) := False;



(* Bound[f] gives an upper bound on the absolute value of a bounded
   function f. *)


Bound /: (Bound[_] < 0) := False;

Bound /: (Bound[_] <= 0) := False;

Bound /: (0 < Bound[_]) := True;

Bound /: (0 <= Bound[_]) := True;

