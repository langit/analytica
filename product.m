(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

SimplifyProduct[f_] := f //. ProductRules;


product[f_, {v_, n1_, n2_}] := Product[f, {v, n1, n2}] /; IntegerQ[n2-n1];


ProductRules := {

(* Rules for simplifying products. *)

product[f_, {v_, n1_, (n2_ + n3_) n_Integer}] :>
        product[f, {v, n1, n2 n + n3 n}],

product[f_, {v_, n1_, n2_+n_Integer?Positive}] :>
        Product[f, {v, n2 + 1, n2 + n}] product[f, {v, n1, n2}],

product[v_, {v_, n1_, n2_}] :> n2! / n1! /; integer[n1] && integer[n2],


(* Rules for simplifying factorials. *)

(n0_+n_Integer?Positive)! :>
        (n0+n-1)! (n0+n),

(n0_+n_Integer?Negative)! :>
        (n0+n+1)! / (n0+n+1),

n_! :> infinity /; WeakSimplify[n<0]

};
