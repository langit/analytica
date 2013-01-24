(* Copyright E.M.Clarke and Xudong Zhao, Jan 22, 1991 *)

(* COMPLEX NUMBERS *)

(* The complex numbers provided by Mathematica are only
suitable for numerical computations. We have provided our
own for symbolic computations. *)

complex/: (complex[a_, b_] + c_) :=  
	complex[a + c, b] /; real[c];

complex/: (complex[a_, b_] + complex[c_, d_]) :=  
	complex[a + c, b + d];

complex/: (complex[a_, b_] c_) :=  
	complex[a c, b c] /; real[c];

complex/: (over[complex[a_, b_], c_]) := 
	complex[over[a,c], over[b,c]] /; real[c];

complex/: (complex[a_, b_] complex[c_, d_]) :=  
	complex[a c - b d, a d + b c];

complex/: (complex[a_, b_] == complex[c_, d_]) :=  and[a == c, b == d];

complex/: (complex[a_, b_] == c_) :=  and[a == c, b == 0] /; real[c];

complex/: (c_ == complex[a_, b_]) :=  and[a == c, b == 0] /; real[c];

complex[x_, 0] := x;

i = complex[0, 1];



(* real part or imaginary part of a complex number *)

Rpart[complex[a_, b_]] := a;

Rpart[x_ + y_] := Rpart[x] + Rpart[y];

Rpart[x_] := x /; real[x];

Ipart[complex[a_, b_]] := b;

Ipart[x_ + y_] := Ipart[x] + Ipart[y];

Ipart[x_] := 0 /; real[x];


