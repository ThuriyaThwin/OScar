% This file contains redefinitions of standard builtins that can be overridden
% by solvers.
include "maximum_int.mzn";
include "minimum_int.mzn";
predicate bool_clause_reif(array[int] of var bool: as,
                           array[int] of var bool: bs,
                           var bool: b);

predicate array_int_maximum(var int: m, array[int] of var int: x) = maximum_int(m,x);

predicate array_float_maximum(var float: m, array[int] of var float: x) =
    let { int: l = min(index_set(x)),
          int: u = max(index_set(x)),
          float: ly = lb_array(x),
          float: uy = ub_array(x),
          array[l..u] of var ly..uy: y } in
    y[l] = x[l] /\
    m = y[u] /\
    forall (i in l+1 .. u) ( y[i] == max(x[i],y[i-1]) );

predicate array_int_minimum(var int: m, array[int] of var int: x) = minimum_int(m,x);

predicate array_float_minimum(var float: m, array[int] of var float: x) =
    let { int: l = min(index_set(x)),
          int: u = max(index_set(x)),
          float: ly = lb_array(x),
          float: uy = ub_array(x),
          array[l..u] of var ly..uy: y } in
    y[l] = x[l] /\
    m = y[u] /\
    forall (i in l+1 .. u) ( y[i] == min(x[i],y[i-1]) );
