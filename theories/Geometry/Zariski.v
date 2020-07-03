Require Import Basics Types WildCat.
Require Import Geometry.Site Geometry.Presheaf Geometry.Sheaf.
Require Import Algebra.Rings.
Require Import Colimits.Quotient.
Require Import Spaces.Finite.

Local Open Scope mc_scope.

Section AssumeFunext.
Context `{Funext}.

  (** For a cover to be a Zariski cover, we require the following: *)
  Class IsZariskiCover {SpecR : CRing^op} (f : Sink SpecR) := {
    (** The indexing set is finite *)
    iszar_finite : Finite (sink_index f);
    (** A family of elements of SpecR which we will later localize at *)
    iszar_a : sink_index f -> SpecR;
    (** Each map of the cover is a localization at a_i *)
    iszar_islocal (i : sink_index f)
      : IsLocalization _ (mss_single_element _ (iszar_a i)) _ (sink_map f i);
    (** Another family of elements of SpecR *)
    iszar_b : sink_index f -> SpecR;
    (** Such that their "inner product" is 1 *)
    (** TODO: better name *)
    iszar_eq : rng_indexed_sum
      (fun i => cring_mult (iszar_a i) (iszar_b i)) = cring_one;
  }.

  Global Existing Instances iszar_finite iszar_islocal.

  (** TODO: the closure condition for coverages can be made into a type class. *)

  (** The Zariski coverage *)
  Definition ZariskiCoverage : Coverage CRing^op.
  Proof.
    snrapply Build_Coverage.
    1: intros SpecR f; exact (IsZariskiCover f).
    hnf; intros U f iszar_f.
    intros V g.
    snrefine (_;_).
    { snrapply Build_Sink.
      1: exact (sink_index f).
      1: exact _.
      1: exact (fun i => rng_localization V (mss_single_element V (g (iszar_a i)))).
      intro i.
      apply rng_localization_map. }
    simpl.
    snrefine (_;_).
    { snrapply Build_IsZariskiCover; cbn.
      1: exact _.
      1: exact (fun i => g (iszar_a i)).
      { intro i.
        simpl.
        apply islocalization_rng_localization. }
      1: exact (fun i => g (iszar_b i)).
      simpl.
      transitivity (rng_indexed_sum (fun i => g (cring_mult (iszar_a i) (iszar_b i)))).
      { admit. }
      transitivity (g (rng_indexed_sum (fun i => cring_mult (iszar_a i) (iszar_b i)))).
      { admit. }
      refine (ap _ _ @ rng_homo_one g).
      exact iszar_eq. }
    intros i.
    exists i.
    snrefine (_;_).
    { (** This map can be constructed using the universal properties of localization. *)
      simpl in g.
      snrapply (islocalization_rec U (mss_single_element U (iszar_a i))
        (sink_domain f i) (f i)); [assumption | exact _ | |].
      { nrefine (rng_homo_compose _ g).
        apply rng_localization_map. }
      intro s.
      snrapply Build_IsUnit.
      { apply class_of.
        refine (cring_one, _).
        destruct s as [s p].
        exists (g s).
        strip_truncations.
        destruct p as [n p].
        apply tr.
        exists n.
        refine (_ @ rng_homo_pow _ _ _).
        f_ap. }
      { apply qglue.
        unfold eq_fraction.
        simpl.
        srefine (_;_).
        { destruct s as [s p].
          exists (g s).
          strip_truncations.
          apply tr.
          exists p.1.
          refine (ap _ _ @ rng_homo_pow _ _ _).
          exact p.2. }
        simpl.
        refine (ap _ _ @ rng_mult_zero_r _).
        rewrite ? rng_mult_one_r, ? rng_mult_one_l.
        cbv in V.
        rapply plus_negate_r. }
      apply qglue.
      unfold eq_fraction.
      simpl.
      srefine (_;_).
      { destruct s as [s p].
        exists (g s).
        strip_truncations.
        apply tr.
        exists p.1.
        refine (ap _ _ @ rng_homo_pow _ _ _).
        exact p.2. }
      simpl.
      refine (ap _ _ @ rng_mult_zero_r _).
      rewrite ? rng_mult_one_r, ? rng_mult_one_l.
      cbv in V.
      rapply plus_negate_r. }
    intro u.
    by rewrite islocalization_rec_beta.
  Admitted.



  Definition ZariskiSite : Site.
  Proof.
    snrapply (Build_Site CRing^op).
    1-3: exact _.
    { intros x y; simpl.
      apply ishset_cringhomomorphism. }
    exact ZariskiCoverage.
  Defined.

End AssumeFunext.