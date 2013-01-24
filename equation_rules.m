(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)


(* RULES FOR EQUATIONS *)

EquationRules = {


(* Standard form for equalities. *)

Equal[a_, b_, c__] :> and[a==b, Equal[b, c]],

(a_?NumberQ == b_) :> (b==a),



(* Integral domain property. *)

(a_ b_ == 0) :> or[a == 0, b == 0],


(a_ + b_ == c_) :> a + b - c == 0 /; c =!= 0,


(* Remove a common additive term from both sides of an
equation. *)
(*
(x_. + a_ == y_. + a_) :> (x == y), 

(x_. + n_Integer a_ == y_. + m_. a_) :> (x + (n-m) a == y)/;NumberQ[m],

(x_. + n_Rational a_ == y_. + m_. a_) :> (x + (n-m) a == y)/;NumberQ[m],
*)


(* Remove a common factor from both sides of an equation. *)

(x_. a_  ==  y_. a_) :> or[a == 0, x == y], 

(x_. a_^n1_. == y_. a_^n2_.) :> 
	or[a^n1 == 0, x == y a^(n2-n1)],

(x_. a_^(n_Integer?Negative e_.) == y_) :>
	(x == y a^(-n e)),


(* Simplify equalities involving a power *)

(a_ ^ b_ == 1) :> (b == 0) /; WeakSimplify[or[1<a, a<-1, -1<a<1]],

(a_^n_ == 0) :> and[a==0, n>0]

};




