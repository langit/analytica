(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)



(* SOLVE SIMPLE LINEAR EQUALITIES. *)


(* Solve linear equations: "q x + r == 0" is equivalent to
   if[ q == 0, r == 0, x == -r/q ]. Position is used to
   distinguish equations in the conclusion from equations
   in some hypothesis. *)

solve[a_ == b_, position_] :=
   Block[{q, r, var, f}, 

        f = Expand[a-b];

        (* Find a variable which appears linearly in the equation. *)

        (var  = LinearVar[f, position]; 

        (* Return the original equation if no variable is linear. *)

        If[var == 0, Return[a == b]];

        (* Otherwise, solve the equation for that variable. *)

        q = Coefficient[f, var];  r = Simplify[f - q var];

        WeakSimplify[if[q == 0, r == 0, var == - r / q]])];



(* Don't change the formula, if it is not an equation. *)

solve[a_, _] := a;



(* Find a variable that is linear in the given expression.
Var[n] is existentially quantified. Const[n] is universally
quantified. Symbols are free varibles. *)

LinearVar[f:(a_. Var[n_] + c_.), _] := Var[n] /; Linear[f, Var[n]];

LinearVar[f:(a_. Const[n__] + c_.), 0] := Const[n] /; Linear[f, Const[n]];

LinearVar[f:(a_. s_Symbol + c_.), 0] := s /; Linear[f, s];

LinearVar[a_. Var[n_] ^ m_Integer + c_., 0] := 
        Var[n]^m /; FreeQ[{a,c}, Var[n]];

LinearVar[a_. Const[n__] ^ m_Integer + c_., 0] := 
        Const[n]^m /; FreeQ[{a,c}, Const[n]];

LinearVar[a_. s_Symbol ^ m_Integer + c_., 0] := 
        s^m /; FreeQ[{a,c}, s];

LinearVar[__] := 0;



(* Check if a variable is linear in a term. *)

Linear[f_, x_] := PolynomialQ[f, x] && (Exponent[f, x] == 1) ;




(* Solve the equations in a sequent. *)

SolveSequent[seq[h_, c_]] := seq[SolveForHypothesis[h], SolveForConclusion[c]];

SolveSequent[a_] := a;



(* Solve the equations in the hypothesis. *)

SolveForHypothesis[and[h_, rest__]] :=
        and[solve[h, 0], SolveForHypothesis[and[rest]]];

SolveForHypothesis[h_] :=
        solve[h, 0];
        
        

(* Solve equations in the conclusion for existentially
quantified variables. *)

SolveForConclusion[or[c_, rest__]] :=
        or[solve[c, 1], SolveForConclusion[or[rest]]];

SolveForConclusion[c_] :=
        solve[c, 1];
        
        

(* See if the sequent is changed by solving linear equalities.
If so, then re-simplify. *)

SolveEquation[s_] := Block[{s0, s1}, (

        (* Solve equations in the sequent.*)

        s0  =   SolveSequent[s];

        (* If the sequent is changed during this  process,
        then simplify again. *)

        s1 = SimplifyIfChanged[s, s0];
 
        (* If the sequent changed, print it out. *)

        If[s1 =!= s,
                (print["solve linear equation"]; 
                PrintMessage[SimplifyMessage])];

        Return[s1]
)];