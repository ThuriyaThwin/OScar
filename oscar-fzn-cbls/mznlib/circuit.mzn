%-----------------------------------------------------------------------------%
% Constrains the elements of 'x' to define a circuit where 'x[i] = j' means
% that 'j' is the successor of 'i'.
%-----------------------------------------------------------------------------%

include "alldifferent.mzn";

predicate circuit(array[int] of var int: x) = 
    let{
       int: offset = min(index_set(x))-1
    } in circuit_no_offset([x[i]-offset | i in index_set(x)]);

predicate circuit_no_offset(array[int] of var int: x);
predicate circuit_decomp(array[int] of var int: x) = 
    let { set of int: S = index_set(x),
          int: l = min(S),
	  int: n = card(S),
	  array[S] of var 1..n: order
        } in
    alldifferent(x) /\	
    alldifferent(order) /\
    forall(i in S)(x[i] != i) /\ 
    order[l] = 1 /\
    forall(i in S)(order[i] != n -> order[x[i]] = order[i] + 1) /\
    forall(i in S)(order[i] == n -> x[i] = l );

predicate circuit_reif(array[int] of var int: x, var bool: b) = 
    abort("Reified circuit/1 is not supported.");

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%
