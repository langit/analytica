(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* FACTOR EXPRESSIONS IN EQUATIONS AND INEQUALITIES. *)


Factorize[s_] := Block[{s0, s1}, (

	(* Factor expressions appearing in equations and inequalities. *)

	s0 = s /.
	
		 {(a_ == b_) :> (Factor[a-b] == 0),

		  (a_ <= b_) :> (Factor[a-b] <= 0),

		  (a_ <  b_) :> (Factor[a-b] <  0)};

	(* If changed during factorization, simplify the sequent. *)

	s1 = SimplifyIfChanged[s, s0];

	(* If the sequent changed, print it out. *)

	If[s1 =!= s, 
		(print["rewrite as"]; PrintMessage[SimplifyMessage])];

	Return[s1])];

