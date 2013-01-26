(* Copyright Edmund Clarke and Xudong Zhao, Jan 22, 1991 *)

(* QUANTIFIER SIMPLIFICATION AND SKOLEMIZATION *)



(* Convert multi-variable quantifiers into single variable
quantifiers. *)

all[{a_, b___}, f_] := all[a, all[{b}, f]];

all[{}, f_] := f;

some[{a_, b___}, f_] := some[a, some[{b}, f]];

some[{}, f_] := f;


(* Reduce scope of quantifiers when possible. *)

all[x_, f_] := f /; FreeQ[f, x];

all[x_, And[a___, b_, c___]] := And[a, all[x, b], c] /; FreeQ[{a, c}, x];

all[x_, Or[a___, b_, c___]] := Or[a, all[x, b], c] /; FreeQ[{a, c}, x];

all[x_, Not[b_]] := Not[some[x, b]];

all[x_, imp[a_, b_]] := imp[a, all[x, b]] /; FreeQ[a, x];

all[x_, imp[a_, b_]] := imp[some[x, a], b] /; FreeQ[b, x];



some[x_, f_] := f /; FreeQ[f, x];

some[x_, And[a___, b_, c___]] := And[a, some[x, b], c] /; FreeQ[{a, c}, x];

some[x_, Or[a___, b_, c___]] := Or[a, some[x, b], c] /; FreeQ[{a, c}, x];

some[x_, Not[b_]] := Not[all[x, b]];

some[x_, imp[a_, b_]] := imp[a, some[x, b]] /; FreeQ[a, x];

some[x_, imp[a_, b_]] := imp[all[x, a], b] /; FreeQ[b, x];



(* Convert restricted quantifiers into ordinary quantifiers. *)

all[x_, restrict_, f_] := all[x, imp[restrict, f]];

some[x_, restrict_, f_] := some[x, And[f, restrict]];



(* Skolemization Procedure. The first argument is the formula. The
second gives the position of the quantifier within the formula. The
last is the current set of global variables--a Skolem function will
depend on this set. *)

VariableNumber = 0;

Quantifiers = {};

QuantifierNames = {};

AllQuantifier = 1;

SomeQuantifier = -1;

Skolemize[seq[a_, b_], position_, vars_] :=
        seq[Skolemize[a, -position, vars], Skolemize[b, position, vars]];

Skolemize[And[a_, b__], position_, vars_] :=
        And[Skolemize[a, position, vars], Skolemize[And[b], position, vars]];
        
Skolemize[And[a_], position_, vars_] := Skolemize[a, position, vars];

Skolemize[Or[a_, b__], position_, vars_] :=
        Or[Skolemize[a, position, vars], Skolemize[Or[b], position, vars]];
        
Skolemize[Or[a_], position_, vars_] := Skolemize[a, position, vars];

Skolemize[imp[a_, b_], position_, vars_] :=
        imp[Skolemize[a, -position, vars], Skolemize[b, position, vars]];

Skolemize[Not[a_], position_, vars_] := Not[Skolemize[a, -position, vars]];

Skolemize[all[x_, a_],  position_, vars_] :=
	If[Positive[position],
                Universal[x, a, position, vars],
                Existential[x, a, position, vars]];

Skolemize[some[x_, a_],  position_, vars_] :=
         If[Negative[position],
                Universal[x, a, position, vars],
                Existential[x, a, position, vars]];
                
Skolemize[a_, _, _] := a;

Universal[x_, a_, position_, vars_] :=
        Block[{newvar},
        	RecordQuantifier[AllQuantifier, x];
		newvar = Var[V[++VariableNumber]];
               	Skolemize[a /. x -> newvar, position, Append[vars, newvar]]
        ];

Existential[x_, a_, position_, vars_] :=
        Block[{newfun},
        	RecordQuantifier[SomeQuantifier, x];
                newfun = Funct[V[++VariableNumber], vars];
                Skolemize[a /. x -> newfun, position, vars]
        ];
        
RecordQuantifier[type_, name_] :=
	        (AppendTo[Quantifiers, type];
         	AppendTo[QuantifierNames, name]);






(* Add quantifiers back to Skolemized formula for output. *)

PositivePosition = 1;

NegativePosition = -1;

CleanUp[f_] :=
        f /. {Funct[v_, ___] :> v, Var[v_] :> v};

Requantify[_, substitution[a_]] :=  Rename[CleanUp[a]];

Requantify[PositivePosition, f_] :=
        Rename[AddQuantifiers[Quantifiers, CleanUp[f]]];

Requantify[NegativePosition, f_] :=
        Rename[AddQuantifiers[-Quantifiers, CleanUp[f]]];

Rename[f_] := f /. V[n_] :> QuantifierNames[[n]];

AddQuantifiers[{}, f_] := f;

AddQuantifiers[{a___, 1}, f_] :=
        AddQuantifiers[{a}, all[V[Length[{a}]+1], f]];

AddQuantifiers[{a___, -1}, f_] :=
        AddQuantifiers[{a}, some[V[Length[{a}]+1], f]];
