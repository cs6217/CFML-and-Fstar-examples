module Examples

open FStar.Heap
open FStar.ST
module Ref = FStar.Ref

let min_max_plus x y min_ref max_ref
   : ST int
      (fun _ -> True)
      (fun h0 v h1 -> v == x + y /\ modifies (Set.union (only min_ref) (only max_ref)) h0 h1 /\
                   (Ref.sel h1 min_ref == x \/ Ref.sel h1 min_ref == y) /\
                   (Ref.sel h1 max_ref == x \/ Ref.sel h1 max_ref == y) /\
                   (Ref.sel h1 min_ref <= Ref.sel h1 max_ref)) = 
   if x < y 
   then begin 
     Ref.write min_ref x;
     Ref.write max_ref y
   end else begin
     Ref.write min_ref y;
     Ref.write max_ref x
   end;
   x + y

let get ref : 
   ST int (fun _ -> True) 
    (fun h0 v h1 -> v == Ref.sel h0 ref /\ modifies Set.empty h0 h1) = 
    Ref.read ref 

let incr ref  : 
    ST unit (fun _ -> True) 
     (fun h0 _ h1 -> Ref.sel h1 ref == Ref.sel h0 ref + 1 /\ modifies (only ref) h0 h1) = 
     let n = Ref.read ref in
     Ref.write ref (n + 1) 

