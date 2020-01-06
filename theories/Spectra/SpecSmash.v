Require Import Basics Types Pointed Smash Spectrum Freudenthal.
Require Import Truncations.
Import TrM.

Local Open Scope pointed_scope.

Context `{Funext}.

Definition susp_smash (X Y : pType)
  : psusp (Smash X Y) <~>* Smash X (psusp Y).
Proof.
Admitted.

Definition smash_right_functor (X : pType) {A B : pType} (f : A ->* B)
  : Smash X A ->* Smash X B.
Proof.
Admitted.

Definition PrespecSmash (X : pType) (Y : Prespectrum) : Prespectrum.
Proof.
  serapply Build_Prespectrum.
  { intro n.
    exact (Smash X (Y n)). }
  intro n.
  cbn.
  serapply loop_susp_adjoint.
  refine (_ o* susp_smash _ _).
  apply smash_right_functor.
  apply loop_susp_adjoint.
  apply glue.
Defined.

Global Instance isspectrum_prespecsmash (X : pType) (Y : Prespectrum)
  : IsSpectrum (PrespecSmash X Y).
Proof.
  intro n.
  unfold PrespecSmash.
  unfold glue.
  
  ntc_rapply @isequiv_compose.
  { (* This is almost never an equivalence, so this just isn't true *)
Abort.
  