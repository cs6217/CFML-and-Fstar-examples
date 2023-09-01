Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Refs.


Module Basics.

Lemma example_let_spec : forall n,
  SPEC (example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xcf.
  xlet.
  xlet.
  xval.
  xsimpl.
  math.
Admitted.

Lemma incr_spec : forall (p:loc) (n:int),
  SPEC (incr p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n+1)).
Proof using.
  xcf.
  xapp.
  xapp.
  xsimpl.
Qed.

Hint Extern 1 (RegisterSpec incr) => Provide incr_spec.

Lemma succ_using_incr_spec : forall n,
  SPEC (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xcf.
  xapp.
  intros p. 
  xapp.
  xapp.
  xsimpl.
  auto.
Qed.

Lemma incr_one_of_two_spec :
  forall (p q:loc) (n m:int),
  SPEC (incr_one_of_two p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n+1) \* q ~~> m).
Proof using.
  xcf. xapp. xsimpl.
Qed.

Lemma incr_and_ref_spec : forall (p:loc) (n:int),
  SPEC (incr_and_ref p)
    PRE (p ~~> n)
    POST (fun (q:loc) => q ~~> (n+1) \* p ~~> (n+1)).
Proof using.
  xcf. xapp. xapp. xapp. xsimpl.
Qed.


Hint Extern 1 (RegisterSpec (incr_and_ref)) => Provide incr_and_ref_spec.


Lemma incr_and_ref'_spec : forall (p:loc) (n:int),
  SPEC (incr_and_ref p)
    PRE (p ~~> n)
    POST (fun (q:loc) =>
        \exists m, \[m > n] \* q ~~> m \* p ~~> (n+1)).
Proof using.
  xtriple.
  xapp.
  intros q.
  xsimpl.
  math.
Qed.

Lemma repeat_incr_spec : forall p n m,
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + m)).
Proof using.
  intros.
  gen n.
  induction_wf IH: (downto 0) m.
  intros.
  xcf. xif. 
  {  (* then branch *)
    intros C.
    xapp. xapp. { unfold downto. math. } xsimpl. math. }
  { (* else branch *)
    intros C.
    xval. xsimpl.
Abort.

Lemma repeat_incr_spec : forall p n m,
  m >= 0 ->
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + m)).
Proof using.
  introv Hm. gen n Hm. induction_wf IH: (downto 0) m. intros.
  xcf. xif; intros C.
  { xapp. xapp. { hnf. math. } { math. }
    xsimpl. math. }
  { xval. xsimpl. math. }
Qed.

Lemma max_nonneg: forall m, m >= 0 -> max 0 m = m.
Proof.
  intros m Hm. rewrite max_r; auto.
  exact antisym_le_int.
Qed.  

Lemma max_nonpos: forall m, m <= 0 -> max 0 m = 0.
Proof.
  intros m Hm. rewrite max_l; auto.
  exact antisym_le_int.
Qed.  


Lemma repeat_incr'_spec : forall p n m,
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + max 0 m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m; intros.
  xcf. xif; intros C.
  { xapp. xapp. { hnf. math. }
    xsimpl. repeat rewrite max_nonneg; math. }
  { xval. xsimpl. rewrite max_nonpos; math. }
Qed.

End Basics.

Module ExoBasic.

  Lemma double_spec : forall n,
  SPEC (double n)
    PRE \[]
    POST (fun m => (* SOLUTION *) \[m = 2 * n] (* /SOLUTION *)).
  Proof using.
    (* SOLUTION *) xcf. xval. xsimpl. math. (* /SOLUTION *)
  Qed.

  Lemma inplace_double_spec : forall p n,
      SPEC (inplace_double p)
           PRE ((* SOLUTION *) p ~~> n (* /SOLUTION *))
           POSTUNIT ((* SOLUTION *) p ~~> (2 * n) (* /SOLUTION *)).
  Proof using.
    (* SOLUTION *) xcf. xapp. xapp. xapp. xsimpl. math. (* /SOLUTION *)
  Qed.

  Lemma decr_and_incr_spec : forall p q n m,
      SPEC (decr_and_incr p q)
           PRE ((* SOLUTION *) p ~~> n \* q ~~> m (* /SOLUTION *))
           POSTUNIT ((* SOLUTION *) p ~~> (n-1) \* q ~~> (m+1) (* /SOLUTION *)).
  Proof using.
    (* SOLUTION *) xcf. xapp. xapp. xsimpl. (* /SOLUTION *)
  Qed.

  Lemma transfer_spec : forall p q n m,
      n >= 0 ->
      SPEC (transfer p q)
           PRE (p ~~> n \* q ~~> m)
           POSTUNIT ((* SOLUTION *) p ~~> 0 \* q ~~> (n + m) (* /SOLUTION *)).
  Proof using.
    introv N. gen m N. induction_wf IH: (downto 0) n. intros.
    (* SOLUTION *)
    xcf. xapp. xif ;=> C.
    { xapp. xapp. xapp. { hnf. math. } { math. }
      xsimpl. math. }
    { xval. xsimpl. math. math. }
    (* /SOLUTION *)
  Qed.

End ExoBasic.


