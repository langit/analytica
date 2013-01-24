(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* REWRITE USING THE EQUATIONS IN THE HYPOTHESIS. *)


(* Substitution of equals. *)

SubstEquation[s_] := Block[{s0, s1}, (

	(* Try repeatedly to rewrite sequent using given identities. *)

	s0 = FixedPoint[Substitute, s] /. GivenIdentities;

	(* If the sequent changed during equation substitution,
	try to simplify it. *)

	s1 = SimplifyIfChanged[s, s0];

	(* If the sequent has changed, print it out. *)

	If[s1 =!= s,
		(print["substitute using equation"]; 
		PrintMessage[SimplifyMessage])];

	s1)];


(* Substitute using an equation in the hypothesis. The equation should
be kept in the hypothesis after substitution. *)

Substitute[seq[and[h1___, a_  ==  b_, h2___], c_]] := 
	seq[and[h1, h2] /. a -> b, c /. a -> b] /;
	Head[a]==Var || Head[a]==Const || Head[a]==Symbol;

Substitute[seq[a_  ==  b_, c_]] := 
	seq[True, c /. a -> b] /;
	Head[a]==Var || Head[a]==Const || Head[a]==Symbol;

Substitute[seq[and[h1___, a_^n_  ==  b_, h2___], c_]] := 
	seq[and[h1, h2], c] /;
	(Head[a]==Var || Head[a]==Const || Head[a]==Symbol) && 
	FreeQ[{h1, h2, c}, a];

Substitute[seq[a_^n_  ==  b_, c_]] := 
	seq[True, c] /;
	(Head[a]==Var || Head[a]==Const || Head[a]==Symbol) &&
	FreeQ[c, a];

Substitute[seq[and[h1___, a_  ==  b_, h2___], c_]] := 
	seq[and[and[h1, h2] /. a -> b, a == b], c /. a -> b] /;
	!FreeQ[{h1, h2, c}, a];

Substitute[seq[a_  ==  b_, c_]] := 
	seq[a == b, c /. a -> b] /;
	!FreeQ[c, a];

Substitute[s_] := s;


