Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.

From Proofs Require Import MinMaxPlus.
Hint Resolve antisym_le_int.

Lemma min_max_plus_spec : forall (x y : int) (min_ref max_ref: loc),
  SPEC (min_max_plus x y min_ref max_ref)
    PRE (min_ref ~~> 0 \* max_ref ~~> 0)
    POST (fun vl => \[x + y = vl] \* min_ref ~~> min x y \* max_ref ~~> max x y).
Proof using.
  xcf.
  xif.
  - intros Hxlty.
    xapp.
    xapp.
    xvals.
    math.
    rewrite min_l; auto; math.
    rewrite max_r; auto; math.
  - intros Hnxlty.
    assert (x >= y) by math.
    xapp.
    xapp.
    xvals.
    math.
    rewrite min_r; auto; math.
    rewrite max_l; auto; math.
Qed.
