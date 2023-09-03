
let min_max_plus x y min_ref max_ref =
  if x < y
  then (min_ref := x; max_ref := y)
  else (min_ref := y; max_ref := x);
  x + y

