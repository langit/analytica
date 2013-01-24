(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* REALS *)



(* Rules for deciding if the type of a term is real. *)

real[a_ + b_] := real[b] /; real[a];

real[a_ b_] := real[b] /; real[a];

real[a_ ^ _Integer] := True /; real[a];

real[a_ ? NumberQ] :=  (Head[a] =!= Complex);

over[a_, b_?NumberQ] := a/b;
