(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* INTEGERS *)



(* Rules for deciding if the type of a term is integer. *)

integer[a_?NumberQ] := (Head[a] === Integer);

integer[x_ y_] := True /; TrueQ[integer[x]] && TrueQ[integer[y]];

integer[x_ + y_] := integer[x] /; integer[y];

integer[a_ ^ m_] := True /; 
	TrueQ[integer[a]] && TrueQ[integer[m]] && WeakSimplify[0 <= m];



(* odd integers *)

Odd[x_ y_] := and[Odd[x], Odd[y]] /; integer[x] && integer[y];

Odd[x_ ^ y_] := and[Odd[x], integer[y], WeakSimplify[0 <= y]];

Odd[x_Integer] := (Mod[x , 2] != 0);



(* even integers *)

Even[x_ y_] := or[Even[x], Even[y]] /; integer[x] && integer[y];

Even[x_ ^ y_] := and[Even[x], integer[y], WeakSimplify[0 < y]];

Even[x_Integer] := (Mod[x , 2] == 0);



(* rules for the powers of " -1 " *)

Unprotect[Power];

(-1)^(x_?Even y_.) := 1 /; !NumberQ[x] && integer[y];

(-1)^(x_?Odd y_.) := (-1)^y /; !NumberQ[x] && integer[y];

(-1)^(x_ + n_Integer) := (-1)^n (-1)^x;

0^n_ := 0 /; WeakSimplify[n>0];

(a_^b_)^c_ := a^(b c);

(a_ b_)^c_ := a^c b^c;

n_Integer ^ (a_ + m_Integer) := n^m n^a;

x_ ^ ((a_Integer) (c_ + d_)) := x ^ (a c + a d);

Protect[Power];



(* Divisible[a, b] means a is divisible by b *)

Divisible[a_, b_] := integer[a / b];



(* gcd[a, b] gives the greatest common divisor of 'a' and 'b' *)

gcd[a_Integer, b_Integer] := GCD[a, b];
