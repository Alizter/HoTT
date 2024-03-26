Require Import Basics Types Colimits.Pushout.
Require Import DPath PathSquare DPathSquare PathCube.
From HoTT.WildCat Require Import Core Yoneda Universe NatTrans TwoOneCat Square ZeroGroupoid FunctorCat EquivGpd.

Record PushoutRecData {A B C : Type} {f : A -> B} {g : A -> C} {P : Type} := {
  pl : B $-> P;
  pr : C $-> P;
  pg : pl $o f $== pr $o g;
}.

Arguments PushoutRecData {A B C} f g P.
Arguments Build_PushoutRecData {A B C}%type_scope {f g}%function_scope {P}%type_scope (pl pr pg)%function_scope.

Definition pushout_rec {A B C : Type} {f : A -> B} {g : A -> C} {P} (r : PushoutRecData f g P)
  : Pushout f g $-> P
  := Pushout_rec P (pl r) (pr r) (pg r).

Definition pushout_rec_beta_pglue {A B C} {f : A -> B} {g : A -> C} {P} (r : PushoutRecData f g P) (x : A)
  : ap (pushout_rec r) (pglue x) = pg r x
  := Pushout_rec_beta_pglue P (pl r) (pr r) (pg r) x.

Definition pushoutrecdata_fun {A B C} {f : A -> B} {g : A -> C} {P Q} (h : P -> Q) (r : PushoutRecData f g P)
  : PushoutRecData f g Q.
Proof.
  snrapply Build_PushoutRecData.
  - exact (h o pl r).
  - exact (h o pr r).
  - exact (fun x => ap h (pg r x)).
Defined.

Definition pushoutrecdata_pushout {A B C} (f : A -> B) (g : A -> C) : PushoutRecData f g (Pushout f g)
  := Build_PushoutRecData pushl pushr pglue.

Definition pushout_rec_inv {A B C} {f : A -> B} {g : A -> C} {P} (r : Pushout f g -> P)
  : PushoutRecData f g P
  := pushoutrecdata_fun r (pushoutrecdata_pushout f g).

Record PushoutRecPath {A B C : Type} {f : A -> B} {g : A -> C} {P : Type} {r s : PushoutRecData f g P} := {
  hpl : pl r $== pl s;
  hpr : pr r $== pr s;
  hpg : Square (hpl $@R f) (hpr $@R g) (pg r) (pg s);
}.

Arguments PushoutRecPath {A B C f g P} r s.

Definition bundle_pushoutrecpath {A B C} {f : A -> B} {g : A -> C} {P}
  {pl' : B $-> P} {pr' : C $-> P} {pg' pg'' : pl' $o f  $== pr' $o g}
  (h : pg' $== pg'')
  : PushoutRecPath (Build_PushoutRecData pl' pr' pg') (Build_PushoutRecData pl' pr' pg'').
Proof.
  snrapply Build_PushoutRecPath.
  1,2: reflexivity.
  intros a; apply equiv_p1_1q.
  rapply h.
Defined.

Ltac bundle_pushoutrecpath :=
  hnf;
  match goal with |- PushoutRecPath ?F ?G =>
    refine (bundle_pushoutrecpath (pg' := pg F) (pg'' := pg G) _) end.

Definition pushout_rec_beta {A B C} {f : A -> B} {g : A -> C} {P} (r : PushoutRecData f g P)
  : PushoutRecPath (pushout_rec_inv (pushout_rec r)) r
  := bundle_pushoutrecpath (f := f) (g := g) (pushout_rec_beta_pglue r).

(** [pushout_rec_inv] is essentially injective, as a map between 0-groupoids. *)
Definition isinj_pushout_rec_inv {A B C} {f : A -> B} {g : A -> C} {P} {r s : Pushout f g -> P}
  (h : PushoutRecPath (pushout_rec_inv r) (pushout_rec_inv s))
  : r == s.
Proof.
  snrapply Pushout_ind.
  - exact (hpl h).
  - exact (hpr h).
  - intros a.
    nrapply transport_paths_FlFr'.
    exact (hpg h a).
Defined.

(** ** PushoutRecData is a 0-groupoid *)

Global Instance isgraph_pushoutrecdata {A B C} {f : A -> B} {g : A -> C} {P}
  : IsGraph (PushoutRecData f g P)
  := {| Hom := PushoutRecPath |}.

Global Instance is01cat_pushoutrecdata {A B C} {f : A -> B} {g : A -> C} {P}
  : Is01Cat (PushoutRecData f g P).
Proof.
  apply Build_Is01Cat.
  - intro r.
    bundle_pushoutrecpath.
    reflexivity.
  - intros f1 f2 f3 h2 h1.
    snrapply Build_PushoutRecPath.
    + exact (hpl h1 $@ hpl h2).
    + exact (hpr h1 $@ hpr h2).
    + snrapply vconcat.
      * exact _.
      * exact (pg f2).
      * exact (hpg h1).
      * exact (hpg h2).
Defined.

Global Instance is0gpd_pushoutrecdata {A B C} {f : A -> B} {g : A -> C} {P}
  : Is0Gpd (PushoutRecData f g P).
Proof.
  apply Build_Is0Gpd.
  intros r s p.
  snrapply Build_PushoutRecPath.
  - exact (hpl p)^$.
  - exact (hpr p)^$.
  - change (Square (hpl p $@R f)^$ (hpr p $@R g)^$ (pg s) (pg r)).
    apply vinverse'.
    exact (hpg p).
Defined.

Definition pushoutrecdata_0gpd {A B C} (f : A -> B) (g : A -> C) P : ZeroGpd
  := Build_ZeroGpd (PushoutRecData f g P) _ _ _.

Global Instance is0functor_pushoutrecdata_fun {A B C} {f : A -> B} {g : A -> C} {P Q}
  (h : P -> Q)
  : Is0Functor (@pushoutrecdata_fun A B C f g P Q h).
Proof.
  apply Build_Is0Functor.
  intros f1 f2 p.
  change (P $-> Q) in h.
  snrapply Build_PushoutRecPath.
  - exact (h $@L hpl p).
  - exact (h $@L hpr p).
  - exact (fmap_square (cat_postcomp _ h) (hpg p)).
Defined.

Global Instance is0functor_pushoutrecdata_0gpd {A B C} {f : A -> B} {g : A -> C}
  : Is0Functor (pushoutrecdata_0gpd f g).
Proof.
  apply Build_Is0Functor.
  intros P Q h.
  snrapply Build_Morphism_0Gpd.
  - exact (pushoutrecdata_fun h).
  - apply is0functor_pushoutrecdata_fun.
Defined.

Global Instance is1functor_pushoutrecdata_0gpd {A B C} {f : A -> B} {g : A -> C}
  : Is1Functor (pushoutrecdata_0gpd f g).
Proof.
  apply Build_Is1Functor.
  - intros P Q g1 g2 p q.
    snrapply Build_PushoutRecPath.
    + exact (p $@R _).
    + exact (p $@R _).
    + intros a; cbn.
      apply moveR_pM, ap_homotopic.
  - intros P r.
    bundle_pushoutrecpath.
    intros a; cbn.
    apply ap_idmap.
  - intros P Q R r s p.
    bundle_pushoutrecpath.
    intros a; cbn.
    apply ap_compose.
Defined.

Definition pushoutrecdata_0gpd_fun {A B C} (f : A -> B) (g : A -> C)
  : Fun11 Type ZeroGpd
  := Build_Fun11 _ _ (pushoutrecdata_0gpd f g).

Definition pushout_nattrans_recdata {A B C P} {f : A -> B} {g : A -> C}
  (r : PushoutRecData f g P)
  : NatTrans (opyon_0gpd P) (pushoutrecdata_0gpd_fun f g).
Proof.
  snrapply Build_NatTrans.
  1: rapply opyoneda_0gpd.
  2: exact _.
  exact r.
Defined.

Definition pushout_rec_inv_nattrans {A B C} (f : A -> B) (g : A -> C)
  : NatTrans (opyon_0gpd (Pushout f g)) (pushoutrecdata_0gpd_fun f g)
  := pushout_nattrans_recdata (pushoutrecdata_pushout f g).

Definition pushout_rec_inv_natequiv {A B C} (f : A -> B) (g : A -> C)
  : NatEquiv (opyon_0gpd (Pushout f g)) (pushoutrecdata_0gpd_fun f g).
Proof.
  snrapply Build_NatEquiv'.
  1: apply pushout_rec_inv_nattrans.
  intros P.
  apply isequiv_0gpd_issurjinj.
  apply Build_IsSurjInj.
  - intros r; cbn in f.
    exists (pushout_rec r).
    apply pushout_rec_beta.
  - exact (@isinj_pushout_rec_inv A B C f g P).
Defined.

Definition pushout_rec_natequiv {A B C} (f : A -> B) (g : A -> C)
  := natequiv_inverse (pushout_rec_inv_natequiv f g).

Global Instance is0functor_pushout_rec {A B C : Type} (f : A $-> B) (g : A $-> C) P
  : Is0Functor (@pushout_rec A B C f g P).
Proof.
  change (Is0Functor (equiv_fun_0gpd (pushout_rec_natequiv f g P))).
  exact _.
Defined.

Definition pushout_rec_nat {A B C} (f : A -> B) (g : A -> C) {P Q} (h : P -> Q)
  (r : PushoutRecData f g P)
  : pushout_rec (pushoutrecdata_fun h r) $== h o pushout_rec r.
Proof.
  exact (isnat (pushout_rec_natequiv f g) h r).
Defined.

Section DoublePushoutRecData.

  (** Throughout this section we assume a 3x3 diagram which can be thought of as a span of spans. We then characterise the recursion data for a double pushout over this double span. This will allow us to prove the 3x3 lemma for pushouts which follows after this section. Note that we state the diagram using wildcat notation as this gives us some precision. If we used [o] for function composition, since it is just a notation, Coq may confuse the morphsisms involved during unification. Using wildcat avoids this issue as it is more rigid. *)
  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : f01 $o f12 $== f10 $o f21) (H13 : f03 $o f12 $== f14 $o f23)
    (H31 : f41 $o f32 $== f30 $o f21) (H33 : f43 $o f32 $== f34 $o f23).

  Let DoublePushout
    := Pushout
        (functor_pushout f21 f01 f41 H11 H31)
        (functor_pushout f23 f03 f43 H13 H33).

  Record DoublePushoutRecData {P : Type} := {
    a00 : A00 $-> P;
    a40 : A40 $-> P;
    a04 : A04 $-> P;
    a44 : A44 $-> P;
    h20 : Square f30 a00 f10 a40;
    h02 : Square f03 a00 f01 a04;
    h24 : Square f34 a04 f14 a44;
    h42 : Square f43 a40 f41 a44;
    dprd_coh
      : Square (A := Hom (A := Type) _ _)
        ((h02 $@R f12) $@ (a04 $@L H13))
        ((a40 $@L H31^$) $@ (h42 $@R f32))
        ((a00 $@L H11) $@ (h20 $@R f21))
        ((h24 $@R f23) $@ (a44 $@L H33^$))
  }.

  Arguments DoublePushoutRecData : clear implicits.
  Arguments Build_DoublePushoutRecData {P}.

  Definition doublepushout_rec {Q : Type}
    : DoublePushoutRecData Q -> DoublePushout $-> Q.
  Proof.
    intros h.
    snrapply Pushout_rec.
    - snrapply Pushout_rec.
      + exact (a00 h).
      + exact (a40 h).
      + exact (h20 h).
    - snrapply Pushout_rec.
      + exact (a04 h).
      + exact (a44 h).
      + exact (h24 h).
    - snrapply Pushout_ind.
      + exact (h02 h).
      + exact (h42 h).
      + intros a.
        nrapply (transport_paths_FlFr' (pglue a)).
        lhs nrapply whiskerR.
        { lhs nrapply ap_compose.
          lhs nrapply ap.
          1: apply functor_pushout_beta_pglue.
          lhs nrapply ap_pp.
          lhs nrapply whiskerL.
          1: nrapply (ap_compose _ _ _)^.
          nrapply whiskerR.
          { lhs nrapply ap_pp.
            lhs nrapply whiskerL.
            1: apply Pushout_rec_beta_pglue.
            nrapply whiskerR.
            1: nrapply (ap_compose pushl _ (H11 a))^. } }
        rhs nrapply whiskerL.
        2: { lhs nrapply (ap_compose (functor_pushout _ _ _ _ _) _ (pglue a)).
          lhs nrapply ap.
          1: apply functor_pushout_beta_pglue.
          lhs nrapply ap_pp.
          lhs nrapply whiskerL.
          1: symmetry; nrapply ap_compose.
          lhs nrapply whiskerR.
          { lhs nrapply ap_pp.
            lhs nrapply whiskerL.
            1: apply Pushout_rec_beta_pglue.
            nrapply whiskerR.
            1: nrapply (ap_compose pushl _ (H13 a))^. }
          apply concat_pp_p. }
        simpl.
        lhs nrapply concat_pp_p.
        rhs nrapply concat_p_pp.
        exact (dprd_coh h a).
  Defined.

  Definition doublepushoutrecdata_fun {P Q}
    (h : P -> Q) (r : DoublePushoutRecData P)
    : DoublePushoutRecData Q.
  Proof.
    change (P $-> Q) in h.
    snrapply Build_DoublePushoutRecData.
    - exact (h $o a00 r).
    - exact (h $o a40 r).
    - exact (h $o a04 r).
    - exact (h $o a44 r).
    - exact (h $@L h20 r).
    - exact (h $@L h02 r).
    - exact (h $@L h24 r).
    - exact (h $@L h42 r).
    - nrapply rewrite_square.
      + exact (fmap_square (cat_postcomp _ h) (dprd_coh r)
          : Square (_ $@L _) (_ $@L _) (_ $@L _) (_ $@L _)).
      + refine (_ $@ (fmap_comp (cat_postcomp _ h) _ _)^$).
        refine (Id _ $@@ _).
        intro; cbn.
        apply ap_compose.
      + refine (_ $@ (fmap_comp (cat_postcomp _ h) _ _)^$).
        refine (_ $@@ Id _).
        intro; cbn.
        apply ap_compose.
      + refine (_ $@ (fmap_comp (cat_postcomp _ h) _ _)^$).
        refine (_ $@@ Id _).
        intro; cbn.
        apply ap_compose.
      + refine (_ $@ (fmap_comp (cat_postcomp _ h) _ _)^$).
        refine (Id _ $@@ _).
        intro; cbn.
        apply ap_compose.
  Defined.

  Definition doublepushoutrecdata_doublepushout
    : DoublePushoutRecData DoublePushout.
  Proof.
    snrapply Build_DoublePushoutRecData.
    - exact (pushl o pushl).
    - exact (pushl o pushr).
    - exact (pushr o pushl).
    - exact (pushr o pushr).
    - exact (fun x => ap pushl (pglue x)).
    - exact (fun x => pglue (pushl x)).
    - exact (fun x => ap pushr (pglue x)).
    - exact (fun x => pglue (pushr x)).
    - simpl. cbn.
      hnf.
      intros x.
      simpl.
      lhs nrapply whiskerL.
      { nrapply whiskerR.
        1: apply ap_compose. }
      lhs nrapply whiskerR.
      { lhs nrapply whiskerR.
        1: apply ap_compose.
        symmetry.
        apply ap_pp. }
      lhs nrapply concat_p_pp.
      lhs nrapply whiskerR.
      { symmetry.
        apply ap_pp. }
      rhs nrapply whiskerL.
      2: { nrapply whiskerL.
        1: apply ap_compose. }
      rhs nrapply concat_pp_p.
      rhs nrapply whiskerL.
      2: { lhs nrapply whiskerR.
        1: apply ap_compose.
        lhs nrapply whiskerL.
        1: symmetry; apply ap_pp.
        symmetry; apply ap_pp. }
      nrefine (whiskerR _ _ @ concat_Ap (pglue
        (f := functor_pushout f21 f01 f41 H11 H31)
        (g := functor_pushout f23 f03 f43 H13 H33)) (pglue x) @ whiskerL _ _).
      + rhs nrapply ap_compose.
        apply ap.
        symmetry.
        rapply functor_pushout_beta_pglue.
      + lhs nrapply ap_compose.
        apply ap.
        rhs nrapply concat_p_pp.
        rapply functor_pushout_beta_pglue.
  Defined.

  Definition doublepushout_rec_inv {P} (r : DoublePushout -> P)
    : DoublePushoutRecData P
    := doublepushoutrecdata_fun r doublepushoutrecdata_doublepushout.

  (** Inlining this coherence can be a pain as the correct typeclasses are not being picked up. Therefore we explicitly state it here and reuse it for the next definition. It should look something like this, but Coq doesn't like that:
  <<
      dprd_coh_coh
      : Square
          (((ha44 $@R f43) $@R f32) $@L dprd_coh r)
          (dprd_coh s $@R ((ha00 $@R f01) $@R f12))
          ((transpose (bifunctor_coh_comp H11 ha00)
            $@h fmap_square (cat_precomp P f21) hh20)
            $@h (transpose (bifunctor_coh_comp H31^$ ha40)
            $@h fmap_square (cat_precomp P f32) hh42))
          ((fmap_square (cat_precomp P f12) hh02
            $@h transpose (bifunctor_coh_comp H13 ha04))
            $@h (fmap_square (cat_precomp P f23) hh24
            $@h transpose (bifunctor_coh_comp H33^$ ha44)))
  >>
  *)
  Definition dprd_coh_coh_type {P : Type} {r s : DoublePushoutRecData P}
    {ha00 : a00 r $== a00 s}
    {ha40 : a40 r $== a40 s}
    {ha04 : a04 r $== a04 s}
    {ha44 : a44 r $== a44 s}
    (hh20 : Square (ha00 $@R f10) (ha40 $@R f30) (h20 r) (h20 s))
    (hh02 : Square (ha00 $@R f01) (ha04 $@R f03) (h02 r) (h02 s))
    (hh24 : Square (ha04 $@R f14) (ha44 $@R f34) (h24 r) (h24 s))
    (hh42 : Square (ha40 $@R f41) (ha44 $@R f43) (h42 r) (h42 s))
    : Type.
  Proof. 
    refine (Square
          (((ha44 $@R f43) $@R f32) $@L dprd_coh r)
          (dprd_coh s $@R ((ha00 $@R f01) $@R f12)) _ _).
    - change (?w $o ?x $-> ?y $o ?z) with (Square z w x y).
      change (Square ?x ?y (?w $o ?z) (?u $o ?v))
        with (Square x y (z $@ w) (v $@ u)).
      repeat srapply hconcat.
      + exact ((ha40 $@R f30) $@R f21).
      + exact ((ha00 $@R f10) $@R f21).
      + apply transpose.
        exact (bifunctor_coh_comp H11 ha00).
      + exact (fmap_square (cat_precomp P f21) hh20).
      + exact ((ha40 $@R f41) $@R f32).
      + apply transpose.
        exact (bifunctor_coh_comp H31^$ ha40).
      + exact (fmap_square (cat_precomp P f32) hh42).
    - change (?w $o ?x $-> ?y $o ?z) with (Square z w x y).
      change (Square ?x ?y (?w $o ?z) (?u $o ?v))
        with (Square x y (z $@ w) (v $@ u)).
      repeat srapply hconcat.
      + exact ((ha04 $@R f14) $@R f23).
      + exact ((ha04 $@R f03) $@R f12).
      + exact (fmap_square (cat_precomp P f12) hh02).
      + apply transpose.
        exact (bifunctor_coh_comp H13 ha04).
      + exact ((ha44 $@R f34) $@R f23).
      + exact (fmap_square (cat_precomp P f23) hh24).
      + apply transpose.
        exact (bifunctor_coh_comp H33^$ ha44).
  Defined.

  Record DoublePushoutRecPath {P : Type} {r s : DoublePushoutRecData P} := {
    ha00 : a00 r $== a00 s;
    ha40 : a40 r $== a40 s;
    ha04 : a04 r $== a04 s;
    ha44 : a44 r $== a44 s;
    hh20 : Square (ha00 $@R f10) (ha40 $@R f30) (h20 r) (h20 s);
    hh02 : Square (ha00 $@R f01) (ha04 $@R f03) (h02 r) (h02 s);
    hh24 : Square (ha04 $@R f14) (ha44 $@R f34) (h24 r) (h24 s);
    hh42 : Square (ha40 $@R f41) (ha44 $@R f43) (h42 r) (h42 s);
    dprd_coh_coh : dprd_coh_coh_type hh20 hh02 hh24 hh42
  }.

  Global Arguments DoublePushoutRecPath {P} r s.

  Definition bundle_doublepushoutrecpath {P}
    {a00' : A00 $-> P} {a40' : A40 $-> P} {a04' : A04 $-> P} {a44' : A44 $-> P}
    {h20' : a00' $o f10 $== a40' $o f30}
    {h02' : a00' $o f01 $== a04' $o f03}
    {h24' : a04' $o f14 $== a44' $o f34}
    {h42' : a40' $o f41 $== a44' $o f43}
    {dprd_coh' dprd_coh''
      : Square (A := Hom (A := Type) _ _)
        ((h02' $@R f12) $@ (a04' $@L H13))
        ((a40' $@L H31^$) $@ (h42' $@R f32))
        ((a00' $@L H11) $@ (h20' $@R f21))
        ((h24' $@R f23) $@ (a44' $@L H33^$))}
    (h : dprd_coh' == dprd_coh'')
    : DoublePushoutRecPath
        (Build_DoublePushoutRecData a00' a40' a04' a44' h20' h02' h24' h42' dprd_coh')
        (Build_DoublePushoutRecData a00' a40' a04' a44' h20' h02' h24' h42' dprd_coh'').
  Proof.
    cbn in dprd_coh'.
    cbn in dprd_coh''.
    snrapply Build_DoublePushoutRecPath.
    1-4: reflexivity.
    1-4: exact (fun _ => concat_p1_1p _).
    simpl.
    unfold dprd_coh_coh_type.
    simpl.
    intros x.
    simpl.
    unfold "$@R", "$@L".
    simpl.
    destruct (h x).
    unfold transpose.
    unfold fmap_square.
    unfold fmap_comp.
    unfold "$@h".
    simpl.
    clear.
    generalize (dprd_coh' x); clear dprd_coh'; intros dprd_coh'.
    generalize (h42' (f32 x)).
    simpl.
    clear.
    
    
    set (r := H11 x) in *.
    clear r.
    (* TODO: coh of coh *)
  Admitted.

  Ltac bundle_doublepushoutrecpath :=
    hnf;
    match goal with |- DoublePushoutRecPath ?F ?G =>
      refine (bundle_doublepushoutrecpath
        (a00' := a00 F) (a40' := a40 F) (a04' := a04 F) (a44' := a44 F)
        (h20' := h20 F) (h02' := h02 F) (h24' := h24 F) (h42' := h42 F) _) end.

  Definition doublepushout_rec_beta {P} (r : DoublePushoutRecData P)
    : DoublePushoutRecPath (doublepushout_rec_inv (doublepushout_rec r)) r.
  Proof.
    snrapply Build_DoublePushoutRecPath.
    1-4: reflexivity.
    - intros x.
      apply equiv_p1_1q.
      lhs_V rapply (ap_compose _ (doublepushout_rec r) (pglue x)).
      rapply Pushout_rec_beta_pglue.
    - intros x.
      apply equiv_p1_1q.
      nrapply (Pushout_rec_beta_pglue
        (f:=functor_pushout f21 f01 f41 H11 H31)
        (g:=functor_pushout f23 f03 f43 H13 H33)).
    - intros x.
      apply equiv_p1_1q.
      lhs_V rapply (ap_compose _ (doublepushout_rec r) (pglue x)).
      rapply Pushout_rec_beta_pglue.
    - intros x.
      apply equiv_p1_1q.
      nrapply (Pushout_rec_beta_pglue
        (f:=functor_pushout f21 f01 f41 H11 H31)
        (g:=functor_pushout f23 f03 f43 H13 H33)).
    - simpl.
      unfold dprd_coh_coh_type.
      simpl. cbn.
  Defined.

  Definition Pushout_ind_FlFr {A B C : Type} {f : A -> B} {g : A -> C}
    {P : Type} (r s : Pushout f g -> P)
    (Hl : forall a, r (pushl a) = s (pushl a))
    (Hr : forall a, r (pushr a) = s (pushr a))
    (H : forall x, ap r (pglue x) @ Hr (g x) = Hl (f x) @ ap s (pglue x))
    : r == s.
  Proof.
    apply isinj_pushout_rec_inv.
    snrapply Build_PushoutRecPath.
    - exact Hl.
    - exact Hr.
    - exact H.
  Defined.

  (* TODO *)
  Definition isinj_doublepushout_rec_inv {P} {r s : DoublePushout -> P}
    (h : DoublePushoutRecPath (doublepushout_rec_inv r) (doublepushout_rec_inv s))
    : r == s.
  Proof.
    apply isinj_pushout_rec_inv.
    snrapply Build_PushoutRecPath.
    - apply isinj_pushout_rec_inv.
      snrapply Build_PushoutRecPath.
      + exact (ha00 h).
      + exact (ha40 h).
      + nrapply vconcatL.
        1: cbn; exact (fun x => ap_compose pushl _ _).
        nrapply vconcatR.
        2: cbn; exact (fun x => ap_compose pushl _ _).
        exact (hh20 h).
    - apply isinj_pushout_rec_inv.
      snrapply Build_PushoutRecPath.
      + exact (ha04 h).
      + exact (ha44 h).
      + nrapply vconcatL.
        1: cbn; exact (fun x => ap_compose pushr _ _).
        nrapply vconcatR.
        2: cbn; exact (fun x => ap_compose pushr _ _).
        exact (hh24 h).
    - intros x.
      apply sq_path.
      revert x.
      snrapply Pushout_ind.
      + exact (fun _ => sq_path (hh02 h _)).
      + exact (fun _ => sq_path (hh42 h _)).
      + intros a22.
        apply dp_cu.
        nrapply cu_ccccGG.
        1,2: nrapply ap.
        1,2: symmetry.
        1,2: nrapply (dp_apD_compose (functor_pushout _ _ _ _ _)).
        nrapply cu_ccccGG.
        1,2: nrapply ap.
        1,2: nrapply ap.
        1,2: symmetry.
        1,2: nrapply apD02.
        1,2: rapply functor_pushout_beta_pglue.
        rewrite ? dp_apD_pp.
        rewrite dp_apD_compose.


        nrapply cu_ccccGG.
        1,2: nrapply ap.
        1,2: symmetry.
        1,2: apply whiskerL.
        1,2: apply whiskerL.
        1,2: simpl.

        rewrite <- apD_compose.
        rewrite (functor_pushout_beta_pglue f21 f01 f41 H11 H31 a22).

  Admitted.

  Global Instance isgraph_doublepushoutrecdata {P}
    : IsGraph (DoublePushoutRecData P)
    := {| Hom := DoublePushoutRecPath |}.

  Global Instance is01cat_doublepushoutrecdata {P}
    : Is01Cat (DoublePushoutRecData P).
  Proof.
    apply Build_Is01Cat.
    - intros r.
      bundle_doublepushoutrecpath.
      reflexivity.
    - intros f1 f2 f3 h2 h1.
      snrapply Build_DoublePushoutRecPath.
      + exact (ha00 h1 $@ ha00 h2).
      + exact (ha40 h1 $@ ha40 h2).
      + exact (ha04 h1 $@ ha04 h2).
      + exact (ha44 h1 $@ ha44 h2).
      + snrapply vconcat.
        * exact (h20 f2).
        * exact (hh20 h1).
        * exact (hh20 h2).
      + snrapply vconcat.
        * exact (h02 f2).
        * exact (hh02 h1).
        * exact (hh02 h2).
      + snrapply vconcat.
        * exact (h24 f2).
        * exact (hh24 h1).
        * exact (hh24 h2).
      + snrapply vconcat.
        * exact (h42 f2).
        * exact (hh42 h1).
        * exact (hh42 h2).
    (* TODO: coh of coh *)
  Defined.

  Global Instance is0gpd_doublepushoutrecdata {P}
    : Is0Gpd (DoublePushoutRecData P).
  Proof.
    apply Build_Is0Gpd.
    intros r s p.
    snrapply Build_DoublePushoutRecPath.
    - exact (ha00 p)^$.
    - exact (ha40 p)^$.
    - exact (ha04 p)^$.
    - exact (ha44 p)^$.
    - change (Square (A := Hom (A := Type) _ _) (ha00 p $@R f10)^$ (ha40 p $@R f30)^$ (h20 s) (h20 r)).
      apply vinverse'.
      exact (hh20 p).
    - change (Square (A := Hom (A := Type) _ _) (ha00 p $@R f01)^$ (ha04 p $@R f03)^$ (h02 s) (h02 r)).
      apply vinverse'.
      exact (hh02 p).
    - change (Square (A := Hom (A := Type) _ _) (ha04 p $@R f14)^$ (ha44 p $@R f34)^$ (h24 s) (h24 r)).
      apply vinverse'.
      exact (hh24 p).
    - change (Square (A := Hom (A := Type) _ _) (ha40 p $@R f41)^$ (ha44 p $@R f43)^$ (h42 s) (h42 r)).
      apply vinverse'.
      exact (hh42 p).
    (* TODO: coh of coh *)
  Defined.

  Definition doublepushoutrecdata_0gpd P : ZeroGpd
    := Build_ZeroGpd (DoublePushoutRecData P) _ _ _.

  Global Instance is0functor_doublepushoutrecdata_fun {P Q}
    (h : P -> Q)
    : Is0Functor (@doublepushoutrecdata_fun P Q h).
  Proof.
    apply Build_Is0Functor.
    intros f1 f2 p.
    change (P $-> Q) in h.
    snrapply Build_DoublePushoutRecPath.
    - exact (h $@L ha00 p).
    - exact (h $@L ha40 p).
    - exact (h $@L ha04 p).
    - exact (h $@L ha44 p).
    - exact (fmap_square (cat_postcomp _ h) (hh20 p)).
    - exact (fmap_square (cat_postcomp _ h) (hh02 p)).
    - exact (fmap_square (cat_postcomp _ h) (hh24 p)).
    - exact (fmap_square (cat_postcomp _ h) (hh42 p)).
    (* TODO: coh of coh *)
  Defined.

  Global Instance is0functor_doublepushoutrecdata_0gpd
    : Is0Functor doublepushoutrecdata_0gpd.
  Proof.
    apply Build_Is0Functor.
    intros P Q h.
    snrapply Build_Morphism_0Gpd.
    - exact (doublepushoutrecdata_fun h).
    - apply is0functor_doublepushoutrecdata_fun.
  Defined.

  Global Instance is1functor_doublepushoutrecdata_0gpd
    : Is1Functor doublepushoutrecdata_0gpd.
  Proof.
    apply Build_Is1Functor.
    - intros P Q g1 g2 p q.
      snrapply Build_DoublePushoutRecPath.
      1-4: exact (p $@R _).
      1-4: intros a; cbn.
      1-4: apply moveR_pM.
      1-4: apply ap_homotopic.
    - intros P r.
      snrapply Build_DoublePushoutRecPath.
      1-4: reflexivity.
      1-4: intros x; apply equiv_1p_q1.
      1-4: apply ap_idmap.
    - intros P Q R r s p.
      snrapply Build_DoublePushoutRecPath.
      1-4: reflexivity.
      1-4: intros x; apply equiv_p1_1q.
      1-4: cbn; apply ap_compose.
  Defined.

  Definition doublepushoutrecdata_0gpd_fun : Fun11 Type ZeroGpd
    := Build_Fun11 _ _ doublepushoutrecdata_0gpd.

  Definition doublepushout_nattrans_recdata {P} (r : DoublePushoutRecData P)
    : NatTrans (opyon_0gpd P) doublepushoutrecdata_0gpd_fun.
  Proof.
    snrapply Build_NatTrans.
    1: rapply opyoneda_0gpd.
    2: exact _.
    exact r.
  Defined.

  Definition doublepushout_rec_inv_nattrans
    : NatTrans (opyon_0gpd DoublePushout) doublepushoutrecdata_0gpd_fun
    := doublepushout_nattrans_recdata doublepushoutrecdata_doublepushout.

  Definition doublepushout_rec_inv_natequiv
    : NatEquiv (opyon_0gpd DoublePushout) doublepushoutrecdata_0gpd_fun.
  Proof.
    snrapply Build_NatEquiv'.
    1: apply doublepushout_rec_inv_nattrans.
    intros P.
    apply isequiv_0gpd_issurjinj.
    apply Build_IsSurjInj.
    - intros r; cbn in r.
      exists (doublepushout_rec r).
      apply doublepushout_rec_beta.
    - exact (@isinj_doublepushout_rec_inv P).
  Defined.

  Definition doublepushout_rec_natequiv
    := natequiv_inverse doublepushout_rec_inv_natequiv.

  Global Instance is0functor_doublepushout_rec P
    : Is0Functor (@doublepushout_rec P).
  Proof.
    change (Is0Functor (equiv_fun_0gpd (doublepushout_rec_natequiv P))).
    exact _.
  Defined.

  Definition doublepushout_rec_nat {P Q} (h : P -> Q) (r : DoublePushoutRecData P)
    : doublepushout_rec (doublepushoutrecdata_fun h r) $== h o doublepushout_rec r.
  Proof.
    exact (isnat doublepushout_rec_natequiv h r).
  Defined.

End DoublePushoutRecData.

Section Transpose.

  (** We again assume the same 3x3 diagram, however we cannot use the same section as before since we need to generalise over the previously defined terms. *)
  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : f01 $o f12 $== f10 $o f21) (H13 : f03 $o f12 $== f14 $o f23)
    (H31 : f41 $o f32 $== f30 $o f21) (H33 : f43 $o f32 $== f34 $o f23).

  (** We can transpose the data of the diagram for which we take the double pushout recursion data. This can be done in a suitable way that is a morphsims of zero groupoids and furthermore natural in [P]. *)
  Definition doublepushoutrecdata_transpose P
    : doublepushoutrecdata_0gpd_fun H11^$ H31^$ H13^$ H33^$ P
      -> doublepushoutrecdata_0gpd_fun H11 H13 H31 H33 P.
  Proof.
    intros [a00 a40 a04 a44 h20 h02 h24 h44 dprd_coh].
    snrapply (Build_DoublePushoutRecData _ _ _ _ _ a00 a04 a40 a44 h02 h20 h44 h24).
    (** Here we rewrite some of the sides of the square so that we end up with similar terms as those in [dprd_coh]. *)
    nrapply vconcatL.
    { refine (_ $@@ Id _).
      refine ((gpd_rev_rev _)^$ $@ _).
      eapply gpd_rev2.
      exact ((gpd_1functor_V (cat_postcomp A22 a00) _)^$ : _ $== a00 $@L H11^$). }
    nrapply hconcatL.
    { refine (Id _ $@@ _).
      refine ((gpd_rev_rev _)^$ $@ _).
      refine (gpd_rev2 _ $@ _).
      - exact ((gpd_1functor_V (cat_postcomp A22 a40) _)^$ : _ $== a40 $@L H13^$).
      - exact ((gpd_1functor_V (cat_postcomp A22 a40) _)^$ : _ $== a40 $@L H13^$^$). }
    nrapply vconcatR.
    2: { refine (Id _ $@@ _).
      refine ((gpd_rev_rev _)^$ $@ _).
      refine (gpd_rev2 _).
      exact ((gpd_1functor_V (cat_postcomp A22 a44) _)^$ : _ $== a44 $@L H33^$^$). }
    (** The square we need to prove here is the same as [dprd_coh] but we need to shuffle the sides around and flip it. It can be quite tricky to see what is going on, therefore you can uncomment the following to follow along. *)
    (*
    set (A := h02 $@R f21) in *.
    set (B := a04 $@L H31^$) in *.
    set (C := a40 $@L H13^$^$) in *.
    set (D := h44 $@R f23) in *.
    set (E := a00 $@L H11^$) in *.
    set (F := h20 $@R f12) in *.
    set (G := h24 $@R f32) in *.
    set (H := a44 $@L H33^$^$) in *.
    change (Square (F $@ C) (B $@ G) (E^$ $@ A) (D $@ H^$)).
    *)
    apply move_left_bottom.
    nrapply vconcatR.
    2: apply cat_assoc.
    apply move_bottom_left.
    apply move_top_right.
    apply hinverse'.
    apply move_right_top.
    nrapply hconcatL.
    1: apply cat_assoc.
    apply move_left_bottom.
    exact dprd_coh.
  Defined.

  (** This transpose map is a morphism of 0-groupoids, i.e. it is functorial. *)
  Global Instance is0functor_doublepushoutrecdata_transpose P
    : Is0Functor (@doublepushoutrecdata_transpose P).
  Proof.
    apply Build_Is0Functor.
    intros a b r.
    snrapply Build_DoublePushoutRecPath.
    - exact (ha00 _ _ _ _ r).
    - exact (ha04 _ _ _ _ r).
    - exact (ha40 _ _ _ _ r).
    - exact (ha44 _ _ _ _ r).
    - exact (hh02 _ _ _ _ r).
    - exact (hh20 _ _ _ _ r).
    - exact (hh42 _ _ _ _ r).
    - exact (hh24 _ _ _ _ r).
  Defined.

  Definition doublepushoutrecdata_transpose_trans
    : Transformation
        (doublepushoutrecdata_0gpd_fun H11^$ H31^$ H13^$ H33^$)
        (doublepushoutrecdata_0gpd_fun H11 H13 H31 H33).
  Proof.
    intros P.
    snrapply Build_Morphism_0Gpd.
    1: apply doublepushoutrecdata_transpose.
    apply is0functor_doublepushoutrecdata_transpose.
  Defined.

  (** Transposing is natural in [P]. *)
  Definition doublepushoutrecdata_transpose_nattrans
    : NatTrans
        (doublepushoutrecdata_0gpd_fun H11^$ H31^$ H13^$ H33^$)
        (doublepushoutrecdata_0gpd_fun H11 H13 H31 H33).
  Proof.
    snrapply Build_NatTrans.
    1: apply doublepushoutrecdata_transpose_trans.
    intros A B f x.
    simpl.
    snrapply Build_DoublePushoutRecPath.
    1-4: reflexivity.
    1-4: exact (vrefl _).
  Defined.

End Transpose.

Section Pushout3x3.

  (** We again assume the same 3x3 diagram, however we cannot use the same section as before since we need to generalise over the previously defined terms. *)
  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : f01 $o f12 $== f10 $o f21) (H13 : f03 $o f12 $== f14 $o f23)
    (H31 : f41 $o f32 $== f30 $o f21) (H33 : f43 $o f32 $== f34 $o f23).


  (** We can capture all these properties about transposing into a natural equivalence. This will be the core lemma of the 3x3 lemma for pushouts. *)
  Definition doublepushoutrecdata_transpose_natequiv
    : NatEquiv
        (doublepushoutrecdata_0gpd_fun H11^$ H31^$ H13^$ H33^$)
        (doublepushoutrecdata_0gpd_fun H11 H13 H31 H33).
  Proof.
    snrapply Build_NatEquiv'.
    1: apply doublepushoutrecdata_transpose_nattrans.
    intros P.
    apply isequiv_0gpd_issurjinj.
    apply Build_IsSurjInj.
    { intros r; cbn in r.
      snrefine (doublepushoutrecdata_transpose H11^$ H31^$ H13^$ H33^$ P _; _).
      { destruct r as [? ? ? ? ? ? ? ? dprd_coh].
        snrapply Build_DoublePushoutRecData.
        1-8: assumption.
        nrapply (rewrite_square dprd_coh).
        1: refine (Id _ $@@ fmap2 _ _).
        2: refine (fmap2 _ _ $@@ Id _).
        3: refine (fmap2 (cat_postcomp _ a01) _ $@@ Id _).
        4: refine (Id _ $@@ fmap2 (cat_postcomp _ a45) _).
        1-4: apply gpd_rev_rev. }
      snrapply Build_DoublePushoutRecPath.
      1-4: reflexivity.
      1-4: exact (vrefl _). }
    intros x y p.
    simpl in p.
    snrapply Build_DoublePushoutRecPath.
    - exact (ha00 _ _ _ _ p).
    - exact (ha04 _ _ _ _ p).
    - exact (ha40 _ _ _ _ p).
    - exact (ha44 _ _ _ _ p).
    - exact (hh02 _ _ _ _ p).
    - exact (hh20 _ _ _ _ p).
    - exact (hh42 _ _ _ _ p).
    - exact (hh24 _ _ _ _ p).
  Defined.

  (** ** 3x3 lemma for pushouts *)


  (* TODO: redraw *)
  (** The 3x3 Diagram looks like the following:
      A00 <--- A02 ---> A04
       ^     // ^ \\     ^
       |    //  |  \\    |
       |   //   |   \\   |
      A20 <--- A22 ---> A24
       |   \\   |   //   |
       |    \\  |  //    |
       V     \\ V //     V
      A40 <--- A42 ---> A44
  The labels look like this:
      A00 f01 A02 f03 A04
      f10 H11 f12 H13 f14
      A20 f21 A22 f23 A24
      f30 H31 f32 H33 f34
      A40 f41 A42 f43 A44 *)


  Theorem equiv_pushout3x3
    : Pushout
        (functor_pushout f21 f01 f41 H11 H31)
        (functor_pushout f23 f03 f43 H13 H33)
    $<~> Pushout
        (functor_pushout f12 f10 f14 H11^$ H13^$)
        (functor_pushout f32 f30 f34 H31^$ H33^$).
  Proof.
    nrapply opyon_equiv_0gpd.
    nrefine (natequiv_compose _ _).
    2: apply doublepushout_rec_inv_natequiv.
    nrefine (natequiv_compose _ _).
    1: apply doublepushout_rec_natequiv.
    apply doublepushoutrecdata_transpose_natequiv.
  Defined.

End Pushout3x3.
