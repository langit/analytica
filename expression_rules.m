(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* RULES FOR ALGEBRAIC EXPRESSIONS. *)

ExpressionRules = {

(* rules for multiplying by a constant. *)

(a_ + (b_?NumberQ) (c_ + d_)) :> (a + b c + b d),



(* Rules for simplification. *)

(a_ + b_  c_.) / b_ :> a/b + c,

(a_. b_ + c_ b_) :> b(a + c) /; !NumberQ[b],

(a_. b_^k_ + c_. b_^n_) :> b^k (a + c b^(n-k)),



(* Rules for power expressions. *)

(a_ + b_)^n_ :> (-a - b)^n (-1)^n /; WeakSimplify[a+b <= 0]

};

