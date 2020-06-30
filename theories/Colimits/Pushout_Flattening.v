Require Import Basics Types.
Require Import Colimits.Pushout.

Require Import HIT.Flattening.

(** Without univalence *)
Section Flattening.

  Context {A X Y : Type} {f : A -> X} {g : A -> Y}
    (P_X : X -> Type) (P_Y : Y -> Type) (e : forall a, P_X (f a) = P_Y (g a)).

  Local Notation coe := (fun x => equiv_transport idmap _ _ (e x)).

  Definition pushout_family : Pushout f g -> Type
    := Pushout_rec _ P_X P_Y e.

  Definition equiv_pushout_flattening `{Funext}
    : Pushout (functor_sigma f (fun _ => idmap)) (functor_sigma g coe)
    <~> sig pushout_family.
  Proof.
    snrapply equiv_adjointify.
    { snrapply Pushout_rec.
      1: exact (functor_sigma pushl (fun _ => idmap)).
      1: exact (functor_sigma pushr (fun _ => idmap)).
      intros [a p].
      srapply (path_sigma' _ (pglue a)).
      simpl.
      refine (transport_idmap_ap _ pushout_family _ _ (pglue a) _ @ _).
      apply ap10, ap.
      apply Pushout_rec_beta_pglue. }
    { intros [x y]; revert x y.
      srapply Pushout_ind.
      { intros x p.
        exact (pushl (x; p)). }
      { intros y q.
        exact (pushr (y; q)). }
      intros a.
      funext p.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (ap _ (ap _ (transport_idmap_ap _ _ _ _ _ _)) @ _).
      refine (ap _ (ap _ (ap10 (ap _ (ap_V _ _)) _)) @ _).
      refine (ap _ (ap _ (ap10 (ap _ (ap _ _)) _)) @ _).
      1: apply (Pushout_rec_beta_pglue _ _ _ _ a).
      refine (pglue (a; transport idmap (e a)^ p) @ _).
      unfold functor_sigma; apply ap, ap.
      rapply transport_pV. }
    { simpl.
      intros [x y]; revert x y.
      snrapply Pushout_ind.
      1: simpl; reflexivity.
      1: simpl; reflexivity.
      intro a.
      funext p.
      simpl.
      simpl in p.
      rewrite transport_forall.
      rewrite transport_paths_FlFr.
      unfold Pushout_ind.
      simpl.
      Search transport_pV.
      rewrite ap_compose.
      simpl.
      unfold Pushout_ind.
      simpl. (*
      rewrite ap_compose 
      rewrite Pushout_rec_beta_pglue.
      simpl.
      admit. }
    { snrapply Pushout_ind.
      { intros [x p].
        simpl.
        reflexivity. }
      { intros [y q].
        reflexivity. }
      intros [a p]. *)
  Admitted.

End Flattening.




