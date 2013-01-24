(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* RULES FOR THE ABSOLUTE VALUE FUNCTION *)



(* The absolute value function -- real case only. *)

Unprotect[Abs];



(* Simple properties of the absolute value function. *)

Abs /: (Abs[a_] < 0) := False;

Abs /: (Abs[a_] <= 0) := (a == 0);

Abs /: (Abs[a_] == 0) := (a == 0);

Abs /: (0 < Abs[a_]) := not[a==0];

Abs /: (0 <= Abs[a_]) := True;



(* Rules for simplifying expressions involving the absolute
value function. *)

Abs[a_ b_] := Abs[a] Abs[b];

Abs[a_^n_] := Abs[a]^n;

Protect[Abs];



(*  Local rule  used in simplification. *)

AbsRule = {

Abs[a_] :> If[TrueQ[WeakSimplify[a >= 0]], a,
		If[TrueQ[WeakSimplify[a <= 0]], -a,
			Abs[Factor1[a]]]]
};

Factor1[a_] := Factor2[Factor[a]];

Factor2[(-1)^n_ a_. + (x_+y_)^n_ b_.] := Factor2[a + (-x-y)^n b];

Factor2[a_ + b_] :=
	If[Order[Factor[Expand[-a-b]], a+b] > 0, 
	   Abs[Factor[Expand[-a-b]]], 
	   Abs[a+b]];

Factor2[a_] := a;
