From HoTT Require Import Basics.
Require Import Types.Paths Types.Arrow.
Require Import Homotopy.Join.Core Homotopy.Join.SuspDiamond.

Local Open Scope path_scope.

(** * Coherence for comparisons of join-map composites *)

(** The recursor templates below retain their specified beta paths. In particular, [delta] has the computation used for scalar right translation, rather than silently replacing it by another homotopy between the same join maps. Short template names are confined to this module. *)
Module JoinMapCoherence.

(** In these two calculations the scalar paths and the free edge identifications are eliminated first. The remaining unit identity is proved for an arbitrary path; no fixed-boundary join filler is eliminated. *)
Local Definition inverse_change {A B : Type}
  {a a' : A} {b b' : B} (p : a = a') (q : b = b')
  {e : joinl a = joinr b} {f : joinl a' = joinr b'}
  (be : e = jglue a b) (bf : f = jglue a' b')
  : (inverse_natural e f (naturality_change be bf (join_natsq p q)^))^
      @ ((ap_V joinl p)^ @@ 1)
    = (1 @@ (ap_V joinr q)^)
      @ naturality_change bf be (join_natsq p^ q^)^.
Proof.
  destruct p, q.
  revert e be f bf.
  snapply paths_ind_r.
  snapply paths_ind_r.
  cbn [inverse join_natsq ap_V ap].
  generalize (jglue a b); generalize (joinr (A:=A) b).
  intros z r; destruct r; reflexivity.
Defined.

Local Definition refl_change {A B : Type} {a : A} {b : B}
  {e : joinl a = joinr b} (be : e = jglue a b)
  : naturality_change be be (join_natsq 1 1)^
    = concat_p1 e @ (concat_1p e)^.
Proof.
  revert e be; snapply paths_ind_r.
  cbn [join_natsq ap].
  generalize (jglue a b); generalize (joinr (A:=A) b).
  intros z r; destruct r; reflexivity.
Defined.

Section JoinMaps.
  Context {A B : Type} (f : A -> A) (g : B -> B).

  Definition delta (t : A -> A) (u v : B -> B) (d : u == v)
    : functor_join t u == functor_join t v.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact 1.
    - intro b; exact (ap joinr (d b)).
    - intros a b.
      lhs napply (functor_join_beta_jglue t u a b @@ 1).
      rhs napply (1 @@ functor_join_beta_jglue t v a b).
      exact (join_natsq 1 (d b))^.
  Defined.

  Definition commute (t : A -> A) (u : B -> B)
    (pl : forall a, f (t a) = t (f a))
    (pr : forall b, g (u b) = u (g b))
    : functor_join f g o functor_join t u
      == functor_join t u o functor_join f g.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinl (pl a)).
    - intro b; exact (ap joinr (pr b)).
    - intros a b.
      lhs napply (ap_compose (functor_join t u) (functor_join f g)
        (jglue a b) @@ 1).
      lhs napply (ap (ap (functor_join f g))
        (functor_join_beta_jglue t u a b) @@ 1).
      lhs napply (functor_join_beta_jglue f g (t a) (u b) @@ 1).
      rhs napply (1 @@ ap_compose (functor_join f g)
        (functor_join t u) (jglue a b)).
      rhs napply (1 @@ ap (ap (functor_join t u))
        (functor_join_beta_jglue f g a b)).
      rhs napply (1 @@ functor_join_beta_jglue t u (f a) (g b)).
      exact (join_natsq (pl a) (pr b))^.
  Defined.

  Definition delta_refl (t : A -> A) (u : B -> B)
    : forall y, delta t u u (fun _ => 1) y = 1.
  Proof.
    snapply Join_ind.
    - reflexivity.
    - reflexivity.
    - intros a b.
      nrefine (equiv_naturality_transport2 (delta t u u (fun _ => 1))
        (fun y => idpath (functor_join t u y)) (jglue a b) 1 1 _).
      lhs napply concat_p1.
      rhs napply concat_1p.
      lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
      rhs napply concat_Ap_refl.
      lhs napply concat_p_pp.
      apply refl_change.
  Defined.
End JoinMaps.

Definition commute_beta {A B : Type} (f t : A -> A) (g u : B -> B)
  (pl : forall a, f (t a) = t (f a))
  (pr : forall b, g (u b) = u (g b)) (a : A) (b : B)
  : concat_Ap (commute f g t u pl pr) (jglue a b)
    = naturality_change
      ((ap_compose (functor_join t u) (functor_join f g) (jglue a b)
        @ ap (ap (functor_join f g)) (functor_join_beta_jglue t u a b))
        @ functor_join_beta_jglue f g (t a) (u b))
      ((ap_compose (functor_join f g) (functor_join t u) (jglue a b)
        @ ap (ap (functor_join t u)) (functor_join_beta_jglue f g a b))
        @ functor_join_beta_jglue t u (f a) (g b))
      (join_natsq (pl a) (pr b))^.
Proof.
  lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
  lhs napply naturality_prefix.
  lhs napply naturality_prefix.
  rhs napply concat_pp_p.
  napply (ap (fun q => (_ @@ 1) @ q)).
  lhs napply naturality_suffix.
  apply naturality_suffix.
Defined.

Definition commute_inverse {A B : Type} (f t : A -> A) (g u : B -> B)
  (pl : forall a, f (t a) = t (f a))
  (pr : forall b, g (u b) = u (g b))
  : forall y, (commute f g t u pl pr y)^
    = commute t u f g (fun a => (pl a)^) (fun b => (pr b)^) y.
Proof.
  snapply Join_ind.
  - intro a; exact (ap_V joinl (pl a))^.
  - intro b; exact (ap_V joinr (pr b))^.
  - intros a b.
    nrefine (equiv_naturality_transport2
      (fun y => (commute f g t u pl pr y)^)
      (commute t u f g (fun a => (pl a)^) (fun b => (pr b)^))
      (jglue a b) _ _ _).
    lhs napply (concat_Ap_inverse (commute f g t u pl pr) (jglue a b) @@ 1).
    lhs napply (ap (fun n => (inverse_natural _ _ n)^)
      (commute_beta f t g u pl pr a b) @@ 1).
    rhs napply (1 @@ commute_beta t f u g _ _ a b).
    apply inverse_change.
Defined.

(** The corner comparisons use the indicated join triangles, not unspecified equalities between parallel path images. *)
Definition compare_l {A B : Type} (b0 : B) {a a' : A}
  (p : a = a') (q : a' = a)
  : (1 @ (ap (joinl (B:=B)) p)^) @ 1 = ap joinl q.
Proof.
  lhs napply concat_p1.
  lhs napply concat_1p.
  lhs_V napply (ap_V (joinl (B:=B)) p).
  exact ((triangle_h' b0 p^)^ @ triangle_h' b0 q).
Defined.

Definition compare_r {A B : Type} (f : A -> A) (g : B -> B) (a0 : A)
  {u u' v v' : B} (p : u = u') (q : g v' = u') (w : v = v')
  (r : u = g v)
  : (ap (joinr (A:=A)) p @ (ap joinr q)^)
      @ ap (functor_join f g) (ap joinr w)^ = ap joinr r.
Proof.
  lhs_V napply (1 @@ ap (ap (functor_join f g))
    (ap_V (joinr (A:=A)) w)).
  lhs_V napply (1 @@ ap_compose joinr (functor_join f g) w^).
  lhs napply (1 @@ ap_compose g joinr w^).
  lhs_V napply (ap_pV (joinr (A:=A)) _ _ @@ 1).
  lhs_V napply (ap_pp (joinr (A:=A)) _ _).
  lhs_V napply (triangle_v' a0).
  rhs_V napply (triangle_v' a0).
  reflexivity.
Defined.

Local Definition compare_l_refl {A B : Type} (b0 : B)
  {a a' : A} (p : a = a')
  : (1 @ (concat_p1 (1 @ (ap (joinl (B:=B)) p)^)
      @ concat_1p (ap joinl p)^)) @ (ap_V joinl p)^
    = compare_l b0 p p^.
Proof.
  destruct p; unfold compare_l; cbn.
  do 3 (rhs napply concat_1p).
  symmetry; apply concat_Vp.
Defined.

Local Definition compare_r_refl {A B : Type}
  (f : A -> A) (g : B -> B) (a0 : A) {v u : B} (p : g v = u)
  : (1 @ (concat_p1 (1 @ (ap (joinr (A:=A)) p)^)
      @ concat_1p (ap joinr p)^)) @ (ap_V joinr p)^
    = compare_r f g a0 1 p 1 p^.
Proof.
  destruct p; unfold compare_r; cbn.
  do 5 (rhs napply concat_1p).
  rhs napply (1 @@ concat_1p _).
  symmetry; apply concat_Vp.
Defined.

Section Comparison.
  Context `{Funext} {A B : Type} (a0 : A) (b0 : B)
    (f t : A -> A) (g u v : B -> B) (d : u == v)
    (el : forall a, f (t a) = t (f a))
    (er : forall b, g (v b) = v (g b))
    (pl : forall a, t (f a) = f (t a))
    (pr : forall b, u (g b) = g (u b))
    (cl : forall a, (el a)^ = pl a)
    (cr : forall b, (d (g b) @ (er b)^) @ ap g (d b)^ = pr b).

  Let assoc := fun y => delta t u v d (functor_join f g y)
    @ (commute f g t v el er y)^
    @ ap (functor_join f g) (delta t u v d y)^.
  Let other := commute t u f g pl pr.

  (** Comparison on the glue for exactly [compare_l] and [compare_r]. The hypotheses [cl,cr] concern the scalar paths; no truncation or filler uniqueness for the join is assumed. Function extensionality lets us eliminate the free homotopy [d], and the free scalar comparison families, before using the checked identity and inverse computations above. *)
  Definition translation_comparison (a : A) (b : B)
    : concat_Ap assoc (jglue a b) @ (compare_l b0 (el a) (pl a) @@ 1)
      = (1 @@ compare_r f g a0 (d (g b)) (er b) (d b) (pr b))
        @ concat_Ap other (jglue a b).
  Proof.
    unfold assoc, other.
    clear assoc other.
    revert v d er pl pr cl cr.
    snapply (equiv_path_ind (fun v => equiv_ap10 u v)).
    cbn [ap10].
    intros er pl pr cl cr.
    destruct (path_forall _ _ cl).
    assert (cr' : (fun b => (er b)^) = pr).
    { apply path_forall; intro b'.
      exact ((concat_p1 _ @ concat_1p _)^ @ cr b'). }
    destruct cr'.
    pose (E := commute f g t u el er).
    pose (K := fun y =>
      (ap011 (fun p q => (p @ (E y)^) @ ap (functor_join f g) q^)
        (delta_refl t u (functor_join f g y)) (delta_refl t u y)
        @ (concat_p1 _ @ concat_1p _))
      @ commute_inverse f t g u el er y).
    lhs_V napply (1 @@ ap (fun q => q @@ idpath
      (ap (functor_join f g o functor_join t u) (jglue a b)))
      (compare_l_refl b0 (el a))).
    rhs_V napply (ap (fun q => idpath
      (ap (functor_join t u o functor_join f g) (jglue a b)) @@ q)
      (compare_r_refl f g a0 (er b)) @@ 1).
    exact (concat_Ap_homotopic _ _ K (jglue a b)).
  Defined.
End Comparison.

(** ** Comparing a translated composite with a single join map *)

Section Composite.
  Context {A B : Type} (f t l : A -> A) (g u r : B -> B).

  Definition combine
    (pl : forall a, t (f a) = l a) (pr : forall b, u (g b) = r b)
    : functor_join t u o functor_join f g == functor_join l r.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinl (pl a)).
    - intro b; exact (ap joinr (pr b)).
    - intros a b.
      lhs napply (ap_compose (functor_join f g) (functor_join t u)
        (jglue a b) @@ 1).
      lhs napply (ap (ap (functor_join t u))
        (functor_join_beta_jglue f g a b) @@ 1).
      lhs napply (functor_join_beta_jglue t u (f a) (g b) @@ 1).
      rhs napply (1 @@ functor_join_beta_jglue l r a b).
      exact (join_natsq (pl a) (pr b))^.
  Defined.

  Definition split
    (el : forall a, l a = t (f a)) (er : forall b, r b = u (g b))
    : functor_join l r == functor_join t u o functor_join f g.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinl (el a)).
    - intro b; exact (ap joinr (er b)).
    - intros a b.
      lhs napply (functor_join_beta_jglue l r a b @@ 1).
      rhs napply (1 @@ ap_compose (functor_join f g) (functor_join t u)
        (jglue a b)).
      rhs napply (1 @@ ap (ap (functor_join t u))
        (functor_join_beta_jglue f g a b)).
      rhs napply (1 @@ functor_join_beta_jglue t u (f a) (g b)).
      exact (join_natsq (el a) (er b))^.
  Defined.

  Definition split_inverse
    (el : forall a, l a = t (f a)) (er : forall b, r b = u (g b))
    : forall x, (split el er x)^
      = combine (fun a => (el a)^) (fun b => (er b)^) x.
  Proof.
    snapply Join_ind.
    - intro a; exact (ap_V joinl (el a))^.
    - intro b; exact (ap_V joinr (er b))^.
    - intros a b.
      nrefine (equiv_naturality_transport2
        (fun x => (split el er x)^)
        (combine (fun a => (el a)^) (fun b => (er b)^))
        (jglue a b) _ _ _).
      lhs napply (concat_Ap_inverse (split el er) (jglue a b) @@ 1).
      rhs napply (1 @@ Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
      assert (be : concat_Ap (split el er) (jglue a b)
        = naturality_change (functor_join_beta_jglue l r a b)
          ((ap_compose (functor_join f g) (functor_join t u) (jglue a b)
            @ ap (ap (functor_join t u)) (functor_join_beta_jglue f g a b))
            @ functor_join_beta_jglue t u (f a) (g b))
          (join_natsq (el a) (er b))^).
      { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
        rhs napply concat_pp_p.
        napply whiskerL.
        lhs napply naturality_suffix.
        apply naturality_suffix. }
      lhs napply (ap (fun n => (inverse_natural _ _ n)^) be @@ 1).
      rhs napply (1 @@ naturality_prefix _ _ _ _).
      rhs napply (1 @@ naturality_prefix _ _ _ _).
      rhs napply (1 @@ concat_p_pp _ _ _).
      apply inverse_change.
  Defined.
End Composite.

Definition compare_r_prefix {A B : Type} (a0 : A)
  {u u' v : B} (p : u = u') (q : v = u') (r : u = v)
  : (ap (joinr (A:=A)) p @ (ap joinr q)^) @ 1 = ap joinr r.
Proof.
  lhs napply concat_p1.
  lhs_V napply (ap_pV (joinr (A:=A)) p q).
  lhs_V napply (triangle_v' a0).
  rhs_V napply (triangle_v' a0).
  reflexivity.
Defined.

Local Definition compare_r_prefix_refl {A B : Type} (a0 : A)
  {v u : B} (p : v = u)
  : (1 @ (concat_p1 (1 @ (ap (joinr (A:=A)) p)^)
      @ concat_1p (ap joinr p)^)) @ (ap_V joinr p)^
    = compare_r_prefix a0 1 p p^.
Proof.
  destruct p; unfold compare_r_prefix; cbn.
  do 2 (rhs napply concat_1p).
  rhs napply (1 @@ concat_1p _).
  symmetry; apply concat_Vp.
Defined.

Section CompositeComparison.
  Context `{Funext} {A B : Type} (a0 : A) (b0 : B)
    (f t l : A -> A) (g u v r : B -> B) (d : u == v)
    (el : forall a, l a = t (f a)) (er : forall b, r b = v (g b))
    (pl : forall a, t (f a) = l a) (pr : forall b, u (g b) = r b)
    (cl : forall a, (el a)^ = pl a)
    (cr : forall b, d (g b) @ (er b)^ = pr b).

  Definition translated_composite_comparison (a : A) (b : B)
    : concat_Ap (fun x =>
        (delta t u v d (functor_join f g x)
          @ (split f t l g v r el er x)^) @ 1) (jglue a b)
        @ (compare_l b0 (el a) (pl a) @@ 1)
      = (1 @@ compare_r_prefix a0 (d (g b)) (er b) (pr b))
        @ concat_Ap (combine f t l g u r pl pr) (jglue a b).
  Proof.
    revert v d er pl pr cl cr.
    snapply (equiv_path_ind (fun v => equiv_ap10 u v)).
    cbn [ap10].
    intros er pl pr cl cr.
    destruct (path_forall _ _ cl).
    assert (cr' : (fun b => (er b)^) = pr).
    { apply path_forall; intro b'.
      exact ((concat_1p _)^ @ cr b'). }
    destruct cr'.
    pose (E := split f t l g u r el er).
    pose (K := fun x =>
      (ap (fun p => (p @ (E x)^) @ 1)
        (delta_refl t u (functor_join f g x))
        @ (concat_p1 _ @ concat_1p _))
      @ split_inverse f t l g u r el er x).
    lhs_V napply (1 @@ ap (fun q => q @@ idpath
      (ap (functor_join l r) (jglue a b)))
      (compare_l_refl b0 (el a))).
    rhs_V napply (ap (fun q => idpath
      (ap (functor_join t u o functor_join f g) (jglue a b)) @@ q)
      (compare_r_prefix_refl a0 (er b)) @@ 1).
    exact (concat_Ap_homotopic _ _ K (jglue a b)).
  Defined.
End CompositeComparison.
(** ** Translating a map which exchanges the join factors *)

Local Definition inverse_change_turn {A B : Type}
  {a a' : A} {b b' : B} (p : a = a') (q : b = b')
  {e : joinr b = joinl a} {f : joinr b' = joinl a'}
  (be : e = (jglue a b)^) (bf : f = (jglue a' b')^)
  : (inverse_natural e f (naturality_change be bf
        (inverse_natural _ _ (join_natsq p q))))^
      @ ((ap_V joinr q)^ @@ 1)
    = (1 @@ (ap_V joinl p)^) @ naturality_change bf be
        (inverse_natural _ _ (join_natsq p^ q^)).
Proof.
  destruct p, q.
  revert e be f bf.
  snapply paths_ind_r.
  snapply paths_ind_r.
  cbn [inverse join_natsq ap_V ap].
  generalize (jglue a b); generalize (joinr (A:=A) b).
  intros z r; destruct r; reflexivity.
Defined.

Section Turn.
  Context {A B : Type} (f : A -> B) (g : B -> A)
    (t : A -> A) (u : B -> B).
  Let rho := join_turn f g.
  Let brho := fun a b => Join_rec_beta_jglue _ _
    (fun a b => (jglue (g b) (f a))^) a b.

  Definition turn_commute
    (el : forall b, g (u b) = t (g b))
    (er : forall a, f (t a) = u (f a))
    : rho o functor_join t u == functor_join t u o rho.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinr (er a)).
    - intro b; exact (ap joinl (el b)).
    - intros a b.
      lhs napply (ap_compose (functor_join t u) rho (jglue a b) @@ 1).
      lhs napply (ap (ap rho) (functor_join_beta_jglue t u a b) @@ 1).
      lhs napply (brho (t a) (u b) @@ 1).
      rhs napply (1 @@ ap_compose rho (functor_join t u) (jglue a b)).
      rhs napply (1 @@ ap (ap (functor_join t u)) (brho a b)).
      rhs napply (1 @@ ap_V (functor_join t u) (jglue (g b) (f a))).
      rhs napply (1 @@ inverse2 (functor_join_beta_jglue t u (g b) (f a))).
      exact (inverse_natural _ _ (join_natsq (el b) (er a))).
  Defined.

  Definition commute_turn
    (pl : forall a, u (f a) = f (t a))
    (pr : forall b, t (g b) = g (u b))
    : functor_join t u o rho == rho o functor_join t u.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinr (pl a)).
    - intro b; exact (ap joinl (pr b)).
    - intros a b.
      exact (naturality_change
        (((ap_compose rho (functor_join t u) (jglue a b)
          @ ap (ap (functor_join t u)) (brho a b))
          @ ap_V (functor_join t u) (jglue (g b) (f a)))
          @ inverse2 (functor_join_beta_jglue t u (g b) (f a)))
        ((ap_compose (functor_join t u) rho (jglue a b)
          @ ap (ap rho) (functor_join_beta_jglue t u a b))
          @ brho (t a) (u b))
        (inverse_natural _ _ (join_natsq (pr b) (pl a)))).
  Defined.

  Definition turn_commute_inverse
    (el : forall b, g (u b) = t (g b))
    (er : forall a, f (t a) = u (f a))
    : forall y, (turn_commute el er y)^
      = commute_turn (fun a => (er a)^) (fun b => (el b)^) y.
  Proof.
    snapply Join_ind.
    - intro a; exact (ap_V joinr (er a))^.
    - intro b; exact (ap_V joinl (el b))^.
    - intros a b.
      nrefine (equiv_naturality_transport2
        (fun y => (turn_commute el er y)^)
        (commute_turn (fun a => (er a)^) (fun b => (el b)^))
        (jglue a b) _ _ _).
      assert (E : concat_Ap (turn_commute el er) (jglue a b)
        = naturality_change
          ((ap_compose (functor_join t u) rho (jglue a b)
            @ ap (ap rho) (functor_join_beta_jglue t u a b))
            @ brho (t a) (u b))
          (((ap_compose rho (functor_join t u) (jglue a b)
            @ ap (ap (functor_join t u)) (brho a b))
            @ ap_V (functor_join t u) (jglue (g b) (f a)))
            @ inverse2 (functor_join_beta_jglue t u (g b) (f a)))
          (inverse_natural _ _ (join_natsq (el b) (er a)))).
      { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
        lhs napply naturality_prefix.
        lhs napply naturality_prefix.
        rhs napply concat_pp_p.
        napply whiskerL.
        do 3 (lhs napply naturality_suffix).
        napply (ap (fun q => inverse_natural _ _ (join_natsq (el b) (er a))
          @ (1 @@ q)^)).
        reflexivity. }
      lhs napply (concat_Ap_inverse (turn_commute el er) (jglue a b) @@ 1).
      lhs napply (ap (fun q => (inverse_natural _ _ q)^) E @@ 1).
      rhs napply (1 @@ Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
      apply inverse_change_turn.
  Defined.
End Turn.

(** This is the left-copy triangle used when the translated map exchanges the factors. *)
Definition compare_turn_l {A B : Type} (b0 : B) (f : A -> B) (g : B -> A)
  {u : A} {v v' : B} (p : g v' = u) (q : v = v') (r : u = g v)
  : (1 @ (ap (joinl (B:=B)) p)^)
      @ ap (join_turn f g) (ap joinr q)^ = ap joinl r.
Proof.
  lhs napply (concat_1p _ @@ 1).
  lhs_V napply (1 @@ ap (ap (join_turn f g)) (ap_V joinr q)).
  lhs_V napply (1 @@ ap_compose joinr (join_turn f g) q^).
  lhs napply (1 @@ ap_compose g joinl q^).
  lhs_V napply (ap_V joinl p @@ 1).
  lhs_V napply (ap_pp joinl _ _).
  lhs_V napply (triangle_h' b0).
  rhs_V napply (triangle_h' b0).
  reflexivity.
Defined.

Local Definition compare_turn_l_refl {A B : Type}
  (b0 : B) (f : A -> B) (g : B -> A) {v : B} {u : A} (p : g v = u)
  : (1 @ (concat_p1 (1 @ (ap (joinl (B:=B)) p)^)
      @ concat_1p (ap joinl p)^)) @ (ap_V joinl p)^
    = compare_turn_l b0 f g p 1 p^.
Proof.
  destruct p; unfold compare_turn_l; cbn.
  do 4 (rhs napply concat_1p).
  rhs napply (1 @@ concat_1p _).
  rhs napply concat_1p.
  rhs napply (1 @@ concat_1p _).
  symmetry; apply concat_Vp.
Defined.

Section TurnComparison.
  Context `{Funext} {A B : Type} (a0 : A) (b0 : B)
    (f : A -> B) (g : B -> A) (t : A -> A) (u v : B -> B) (d : u == v)
    (el : forall b, g (v b) = t (g b))
    (er : forall a, f (t a) = v (f a))
    (pl : forall a, u (f a) = f (t a))
    (pr : forall b, t (g b) = g (u b))
    (cl : forall a, d (f a) @ (er a)^ = pl a)
    (cr : forall b, (el b)^ @ ap g (d b)^ = pr b).

  Definition translation_turn_comparison (a : A) (b : B)
    : concat_Ap (fun y =>
        (delta t u v d (join_turn f g y)
          @ (turn_commute f g t v el er y)^)
        @ ap (join_turn f g) (delta t u v d y)^) (jglue a b)
        @ (compare_r_prefix a0 (d (f a)) (er a) (pl a) @@ 1)
      = (1 @@ compare_turn_l b0 f g (el b) (d b) (pr b))
        @ concat_Ap (commute_turn f g t u pl pr) (jglue a b).
  Proof.
    revert v d el er pl pr cl cr.
    snapply (equiv_path_ind (fun v => equiv_ap10 u v)).
    cbn [ap10].
    intros el er pl pr cl cr.
    assert (cl' : (fun a => (er a)^) = pl).
    { apply path_forall; intro a'.
      exact ((concat_1p _)^ @ cl a'). }
    assert (cr' : (fun b => (el b)^) = pr).
    { apply path_forall; intro b'.
      exact ((concat_p1 _)^ @ cr b'). }
    destruct cl', cr'.
    pose (E := turn_commute f g t u el er).
    pose (K := fun y =>
      (ap011 (fun p q => (p @ (E y)^) @ ap (join_turn f g) q^)
        (delta_refl t u (join_turn f g y)) (delta_refl t u y)
        @ (concat_p1 _ @ concat_1p _))
      @ turn_commute_inverse f g t u el er y).
    lhs_V napply (1 @@ ap (fun q => q @@ idpath
      (ap (join_turn f g o functor_join t u) (jglue a b)))
      (compare_r_prefix_refl a0 (er a))).
    rhs_V napply (ap (fun q => idpath
      (ap (functor_join t u o join_turn f g) (jglue a b)) @@ q)
      (compare_turn_l_refl b0 f g (el b)) @@ 1).
    exact (concat_Ap_homotopic _ _ K (jglue a b)).
  Defined.
End TurnComparison.

(** ** Comparing a translated turn with a different turn *)
Section TurnComposite.
  Context {A B : Type} (f l : A -> B) (g r : B -> A)
    (t : A -> A) (u : B -> B).
  Let rho := join_turn f g.
  Let sigma := functor_join t u.
  Let tau := join_turn l r.
  Let brho := fun a b => Join_rec_beta_jglue _ _
    (fun a b => (jglue (g b) (f a))^) a b.
  Let btau := fun a b => Join_rec_beta_jglue _ _
    (fun a b => (jglue (r b) (l a))^) a b.

  Definition combine_turn
    (pl : forall a, u (f a) = l a) (pr : forall b, t (g b) = r b)
    : sigma o rho == tau.
  Proof.
    snapply Join_ind_FFlFr.
    - intro a; exact (ap joinr (pl a)).
    - intro b; exact (ap joinl (pr b)).
    - intros a b.
      lhs napply (ap (ap sigma) (brho a b) @@ 1).
      lhs napply (ap_V sigma (jglue (g b) (f a)) @@ 1).
      lhs napply (inverse2 (functor_join_beta_jglue t u (g b) (f a)) @@ 1).
      rhs napply (1 @@ btau a b).
      apply moveR_Vp.
      rhs napply concat_p_pp.
      apply moveL_pV.
      exact (join_natsq (pr b) (pl a)).
  Defined.

  Definition split_turn
    (el : forall b, r b = t (g b)) (er : forall a, l a = u (f a))
    : tau == sigma o rho.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinr (er a)).
    - intro b; exact (ap joinl (el b)).
    - intros a b.
      lhs napply (btau a b @@ 1).
      rhs napply (1 @@ ap_compose rho sigma (jglue a b)).
      rhs napply (1 @@ ap (ap sigma) (brho a b)).
      rhs napply (1 @@ ap_V sigma (jglue (g b) (f a))).
      rhs napply (1 @@ inverse2 (functor_join_beta_jglue t u (g b) (f a))).
      exact (inverse_natural _ _ (join_natsq (el b) (er a))).
  Defined.

  Definition split_turn_inverse
    (el : forall b, r b = t (g b)) (er : forall a, l a = u (f a))
    : forall x, (split_turn el er x)^
      = combine_turn (fun a => (er a)^) (fun b => (el b)^) x.
  Proof.
    snapply Join_ind.
    - intro a; exact (ap_V joinr (er a))^.
    - intro b; exact (ap_V joinl (el b))^.
    - intros a b.
      nrefine (equiv_naturality_transport2
        (fun x => (split_turn el er x)^)
        (combine_turn (fun a => (er a)^) (fun b => (el b)^))
        (jglue a b) _ _ _).
      pose (bf := ((ap_compose rho sigma (jglue a b)
        @ ap (ap sigma) (brho a b)) @ ap_V sigma (jglue (g b) (f a)))
        @ inverse2 (functor_join_beta_jglue t u (g b) (f a))).
      assert (be : concat_Ap (split_turn el er) (jglue a b)
        = naturality_change (btau a b) bf
          (inverse_natural _ _ (join_natsq (el b) (er a)))).
      { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
        rhs napply concat_pp_p.
        napply whiskerL.
        do 3 (lhs napply naturality_suffix).
        reflexivity. }
      lhs napply (concat_Ap_inverse (split_turn el er) (jglue a b) @@ 1).
      lhs napply (ap (fun n => (inverse_natural _ _ n)^) be @@ 1).
      rhs napply (1 @@ Join_ind_FFlFr_beta_jglue rho sigma tau _ _ _ a b).
      do 3 (rhs napply (1 @@ naturality_prefix _ _ _ _)).
      rhs napply (1 @@ (1 @@ (inverse_natural_moves _ _ _ @@ 1))).
      rhs napply (1 @@ concat_p_pp _ _ _).
      apply inverse_change_turn.
  Defined.
End TurnComposite.

(** A parameter-dependent turn may be translated on its output and on its scalar parameter simultaneously. Its corner comparisons are the same selected triangles as in [compare_r] and [compare_turn_l]. *)
Section TurnParameterComparison.
  Context `{Funext} {X : Type} (x0 : X)
    (m00 m01 m10 m11 : X -> X -> X)
    (dm : forall a b c d,
      zigzag (m00 a c) (m11 b d) (m01 a d)
        = zigzag (m00 a c) (m11 b d) (m10 b c)).
  Let J := Join X X.
  Let m : J -> J -> J := Join_rec2 J
    (fun a c => joinl (m00 a c)) (fun a d => joinr (m01 a d))
    (fun b c => joinr (m10 b c)) (fun b d => joinl (m11 b d))
    (fun a c d => jglue (m00 a c) (m01 a d))
    (fun b c d => (jglue (m11 b d) (m10 b c))^)
    (fun c a b => jglue (m00 a c) (m10 b c))
    (fun d a b => (jglue (m11 b d) (m01 a d))^) dm.
  Context (s : X) (t u v : X -> X) (d : u == v)
    (el : forall b, m11 b (v s) = t (m11 b s))
    (er : forall a, m01 a (v s) = v (m01 a s))
    (pl : forall a, u (m01 a s) = m01 a (u s))
    (pr : forall b, t (m11 b s) = m11 b (u s))
    (cl : forall a, (d (m01 a s) @ (er a)^) @ ap (m01 a) (d s)^ = pl a)
    (cr : forall b, (el b)^ @ ap (m11 b) (d s)^ = pr b).
  Let f := fun a => m01 a s.
  Let g := fun b => m11 b s.
  Let E := split_turn f (fun a => m01 a (v s)) g
    (fun b => m11 b (v s)) t v el er.
  Let B := combine_turn f (fun a => m01 a (u s)) g
    (fun b => m11 b (u s)) t u pl pr.

  Definition translated_turn_parameter_comparison (a b : X)
    : concat_Ap (fun x =>
        (delta t u v d (join_turn f g x) @ (E x)^)
          @ ap (m x) (ap joinr (d s))^) (jglue a b)
        @ (compare_r (m00 a) (m01 a) x0
          (d (m01 a s)) (er a) (d s) (pl a) @@ 1)
      = (1 @@ compare_turn_l x0 (m10 b) (m11 b) (el b) (d s) (pr b))
        @ concat_Ap B (jglue a b).
  Proof.
    unfold E, B; clear E B.
    revert v d el er pl pr cl cr.
    snapply (equiv_path_ind (fun v => equiv_ap10 u v)).
    cbn [ap10].
    intros el er pl pr cl cr.
    assert (cl' : (fun a => (er a)^) = pl).
    { apply path_forall; intro a'.
      exact ((concat_p1 _ @ concat_1p _)^ @ cl a'). }
    assert (cr' : (fun b => (el b)^) = pr).
    { apply path_forall; intro b'.
      exact ((concat_p1 _)^ @ cr b'). }
    destruct cl', cr'.
    pose (E := split_turn f (fun a => m01 a (u s)) g
      (fun b => m11 b (u s)) t u el er).
    pose (K := fun x =>
      (ap (fun p => (p @ (E x)^) @ 1)
        (delta_refl t u (join_turn f g x))
        @ (concat_p1 _ @ concat_1p _))
      @ split_turn_inverse f (fun a => m01 a (u s)) g
        (fun b => m11 b (u s)) t u el er x).
    lhs_V napply (1 @@ ap (fun q => q @@ idpath
      (ap (join_turn (fun a => m01 a (u s)) (fun b => m11 b (u s)))
        (jglue a b))) (compare_r_refl (m00 a) (m01 a) x0 (er a))).
    rhs_V napply (ap (fun q => idpath
      (ap (functor_join t u o join_turn f g) (jglue a b)) @@ q)
      (compare_turn_l_refl x0 (m10 b) (m11 b) (el b)) @@ 1).
    exact (concat_Ap_homotopic _ _ K (jglue a b)).
  Defined.
End TurnParameterComparison.
End JoinMapCoherence.
