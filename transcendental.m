(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* RULES FOR TRANSCENDENTAL FUNCTIONS *)

(* Cos and Sin are everywhere continuous functions. *)

ContinuousFunction[Sin] = True;

ContinuousFunction[Cos] = True;


(* They are also uniformly continuous. *)

UniformlyContinuous[Sin] = True;

UniformlyContinuous[Cos] = True;


(* Cos and Sin are bounded functions *)

Bounded[Cos] = Bounded[Sin] = True;

Bound[Cos] = Bound[Sin] = 1;


(* Simplify argument of function if possible. *)

Unprotect[Cos, Sin];

Cos[x_] := Cos[Factor[x]]/; Factor[x] =!= x;

Sin[x_] := Sin[Factor[x]]/; Factor[x] =!= x;

Protect[Sin, Cos];

inverse[delta[Cos]][a_] := a;



(* Rules for the logarithm function. *)

Unprotect[Log];

Log/: (Log[a_] == Log[b_]) :=  and[0 < a, a == b];

Log/: (Log[a_] < Log[b_])  :=  and[0 < a, a < b];

Log/: (Log[a_] <= Log[b_]) :=  and[0 < a, a <= b];

Log[a_ b_] := Log[a] + Log[b] /; WeakSimplify[and[a>0, b>0]];

Log[a_ ^ b_] := b Log[a] /; WeakSimplify[a>0];

Protect[Log];

