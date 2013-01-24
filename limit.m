(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* PROPERTIES OF LIMITS AND INFINITY *)

SimplifyLimit[f_] := f //. LimitRules /. power -> Power;



(* Local rules for finding the limit of an expression. *)

LimitRules = {

limit[a_ b_, {m_, l_}] :> a limit[b, {m, l}] /; FreeQ[a, m],

limit[a_ + b_, {m_, l_}] :> a + limit[b, {m, l}] /; FreeQ[a, m],

limit[a_ ^ b_, {m_, l_}] :> 
	limit[a, {m, l}] ^ limit[b, {m, l}] /; FreeQ[a, m] || FreeQ[b, m],

limit[(a_)^(p_) (b_)^(p_), {m_, l_}] :>
	power[limit[a b, {m, l}], limit[p, {m, l}]] /; 
	FreeQ[a b, m] || FreeQ[p, m],



a_ ^ infinity :> power[a, infinity],

a_ ^ (-infinity) :> power[a, -infinity],

infinity ^ a_ :> infinity /; WeakSimplify[a>0],

infinity ^ a_ :> 0 /; WeakSimplify[a<0],

a_ infinity :> infinity /; WeakSimplify[a>0],

a_ infinity :> -infinity /; WeakSimplify[a<0] && a =!= -1,

a_ + b_. infinity :> b infinity /; FreeQ[a, infinity] && FreeQ[a, limit]

};



(* Convergent[f] is True if f has a finite value. *)

Convergent[a_. infinity] := False;

Convergent[a_] := True /; 
	FreeQ[a, Var] && FreeQ[a, limit] && FreeQ[a, infinity];

limit[m_, {m_, l_}] := l;

limit[a_, {m_, l_}] := a /; FreeQ[a, m];

infinity /: (infinity < _) := False;

infinity /: (_ <= infinity) := True;

infinity /: (infinity <= _) := False;

infinity /: (_ < infinity) := True;



(* Rules for expressions that involve infinity in some exponent. *)

power[a_, b_] := a^b /; FreeQ[b, infinity] && FreeQ[b, limit];

power[a_, infinity] := 
	If[TrueQ[WeakSimplify[a>1]], infinity, 0] /; 
	WeakSimplify[or[a>1, and[a < 1, a > -1]]];

power[a_, -infinity] := 
	If[TrueQ[WeakSimplify[a>1]], 0, infinity] /; 
	WeakSimplify[or[a>1, and[a < 1, a > -1]]];


