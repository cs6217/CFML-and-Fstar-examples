module DjikstraMonad
(*
   Modified from fstar repo https://github.com/FStarLang/FStar/blob/master/examples/oplss2021/OPLSS2021.DijkstraMonads.fst

   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

open FStar.Monotonic.Pure

let wp0 (st:Type0) (a:Type) = st -> (a & st -> Type) -> Type

let st_monotonic #st #a (w : wp0 st a) : prop =
  forall (s0:st)
    (p1 p2: (a & st -> Type)).
    (forall x s1. p1 (x, s1) ==> p2 (x, s1)) ==>
    w s0 p1 ==>
    w s0 p2

let wp st a = w:wp0 st a{st_monotonic w}

unfold
let return_wp (#a:Type) (#st:Type0) (x:a)
  : wp st a
  = fun s0 p -> p (x, s0)

unfold
let bind_wp (#a #b:Type) (#st:Type0)
            (wp_c:wp st a)
            (wp_f:a -> wp st b)
  : wp st b
  = fun s0 p ->
      wp_c s0
      //push the postcondition of the continuation
      //through the WP transformer of c
      (fun (y, s1) ->
        //push the postcondition p
        //through the WP transformer of f applied to the
        //result value and state of c
        wp_f y s1 p)


let repr (a:Type) (st:Type0) (wp : wp st a) : Type =
  s0:st -> PURE (a & st) (as_pure_wp (wp s0))


let return (a:Type) (x:a) (st:Type0)
  : repr a st (return_wp x)
  = fun s0 -> (x, s0)

let bind (a:Type) (b:Type) (st:Type0)
         (wp_c : wp st a)
         (wp_f : a -> wp st b)
         (c : repr a st wp_c)
         (f : (x:a -> repr b st (wp_f x)))
  : repr b st (bind_wp wp_c wp_f)
  = fun s0 -> let (y, s1) = c s0 in
           f y s1

let stronger
  (#a:Type) (#st:Type0)
  (w1 w2 : wp st a)
  : Type0
  = forall s0 p. w1 s0 p ==> w2 s0 p

let subcomp
  (a:Type)
  (st:Type0)
  (wpf wpg : wp st a)
  (f : repr a st wpf)
  : Pure (repr a st wpg)
         (requires (stronger wpg wpf))
         (ensures (fun _ -> True))
  = f

total
reifiable
reflectable
layered_effect {
  ST : a:Type -> st:Type0 -> wp st a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp
}


let pure a wp = unit -> PURE a wp

unfold
let lift_wp (#a:Type) (#st:Type0) (w:pure_wp a) : wp st a =
  elim_pure_wp_monotonicity_forall ();
  fun s0 p -> w (fun x -> p (x, s0))

let lift_pure_st a st wp (f : pure a wp)
  : repr a st (lift_wp wp)
  = elim_pure_wp_monotonicity_forall ();
    fun s0 -> (f (), s0)

sub_effect PURE ~> ST = lift_pure_st


let get #st ()
  : ST st st (fun s0 p -> p (s0, s0))
  = ST?.reflect (fun s0 -> (s0, s0))


let put #st (s:st)
  : ST unit st (fun _ p -> p ((), s))
  = ST?.reflect (fun _ -> ((), s))

let as_wp (a:Type) (st:Type) (pre: st -> prop) (post: st -> a -> st -> prop)
  : wp st a
  = fun s0 k -> pre s0 /\ (forall x s1. post s0 x s1 ==> k (x, s1))

effect HoareST (a:Type) (st:Type) (pre: st -> prop) (post: st -> a -> st -> prop) =
  ST a st (as_wp a st pre post)

let double ()
  : HoareST unit int
    (requires fun _ -> True)
    (ensures fun s0 _ s1 -> s1 == s0 + s0)
  = let x = get () in
    put (x + x)
