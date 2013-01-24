(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* SOME MATHEMATICAL LEMMAS *)

(* Continuity of infinite series. *)

AddLemma[all[{f, n, x, x0, min},

		(* If the summation is continuous term by term *)

	  imp[and[Continuous[f, {x, x0}],

		(* and uniformly convergent over some interval around x0, *)

		  UniformlyConvergent[sum[f, {n, min, infinity}],
				    {x, x0-sigma, x0+sigma}]],

		(* then it is continuous at x0. *)

	      Continuous[sum[f, {n, min, infinity}], {x, x0}]]]];

(* Uniform convergence of infinite series (Weierstrass M-test). *)

AddLemma[all[{f, n, x, c1, c2, min},

		(* If there is some convergent series whose terms are
		   constants with respect to x *)

	  imp[some[f1, and[

		(* and each term is greater than the corresponding term of
		the given series, *)

		       imp[and[c1<x, x<c2], Abs[f]<=f1], IsConstant[f1, x],
			Convergent[sum[f1, {n, min, infinity}]]]],

		(* then the given series is uniformly convergent. *)

	      UniformlyConvergent[sum[f, {n, min, infinity}], 
			{x, c1, c2}]]]];



(* Some sufficient conditions for deciding the sign of a summation. *)

AddLemma[all[{k, low, up, f}, 
	imp[imp[and[low <=k, k<=up], 0<=f],
		0 <= sum[f, {k, low, up}]]]] ;

AddLemma[all[{k, low, up, f}, 
	imp[imp[and[low <=k, k<=up], f<=0],
		sum[f, {k, low, up}] <= 0]]] ;

AddLemma[all[{k, low, up, f}, 
	imp[imp[and[low <=k, k<=up], f == 0],
		sum[f, {k, low, up}] == 0]]] ;

AddLemma[all[{k, low, up, f, cond}, 
	imp[imp[and[low <=k, k<=up, cond], 0<=f],
		0 <= sum[f, {k, low, up, cond}]]]] ;

AddLemma[all[{k, low, up, f, cond}, 
	imp[imp[and[low <=k, k<=up, cond], f<=0],
		sum[f, {k, low, up, cond}] <= 0]]] ;

AddLemma[all[{k, low, up, f, cond}, 
	imp[imp[and[low <=k, k<=up, cond], f == 0],
		sum[f, {k, low, up, cond}] == 0]]] ;



(* Values for the Sin and Cos in particular ranges. *)

AddLemma[all[x, imp[and[x >= -Pi/2, x <= Pi/2], 0 <= Cos[x]]]];

AddLemma[all[x, imp[and[x>=0, x<=Pi], 0 <= Sin[x]]]];

