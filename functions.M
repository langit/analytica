(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* PACKAGE FOR MATHEMATICAL FUNCTIONS *)

BeginPackage["functions`", "UserInterface`", "SystemInterface`"] 

(*  Functions provided to user:

	Continuous (analysis.m)

	round (analysis.m)

	ContinuousFunction (analysis.m)

	UniformlyContinuous (analysis.m)

	UniformlyConvergent (analysis.m)

	IsConstant (analysis.m)

	Increasing (analysis.m)

	Decreasing (analysis.m)

	Bounded (analysis.m)

	Closed (analysis.m)

	ClosedInterval (analysis.m)

	inverse (analysis.m)

	delta (analysis.m)

	Bound (analysis.m)

	Domain (analysis.m)

	sum (summation.m)

	product (product.m)

	limit (limit.m)

	infinity (limit.m)

	Convergent (limit.m)

   Functions needed in other packages but not
   available to the user:

	AbsRule (abs_value.m)

	MaxMinRules (max_min.m)

	SimplifySummation (summation.m)

	SimplifyProduct (product.m)

	SimplifyLimit (limit.m)

	RewriteTrig (trigonometric.m)

	RewriteSum (summation.m)

	TrigSimplify (trigonometric.m)

*)

Begin["FunPrivate`"];

<<GosperSum.m;

<<transcendental.m;

<<abs_value.m;

<<max_min.m;

<<analysis.m;

<<summation.m;

<<product.m;

<<limit.m;

End[]

<<trigonometric.m;

<<congruence.m;

EndPackage[]
