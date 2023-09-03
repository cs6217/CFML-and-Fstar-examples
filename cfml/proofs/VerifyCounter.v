Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.


From Proofs Require Import Counter.


Definition Count (n:int) (g:val) : hprop :=
  \exists p, (p ~~> n) \*
    \[ forall n', SPEC (g tt)
                  PRE (p ~~> n')
                  POST (fun r => \[r = n'] \* (p ~~> (n'+1))) ].

Lemma make_counter_spec :
  SPEC (make_counter tt)
  PRE \[]
  POST (fun c => c ~> Count 0).
Proof.
  xcf.
  xapp;=> i.
  xlet as;=> g Hg.
  asserts g_spec :
     (forall  n', SPEC (g tt)
                    PRE (i ~~> n')
                    POST (fun r => \[r = n'] \* (i ~~> (n'+1)))).
  {
    intros n'; apply Hg.
    xapp.
    xapp.
    xvals*.
  }
  xvals*.
  unfold Count; rewrite (@repr_eq _ _ g); xsimpl*.
Qed.
