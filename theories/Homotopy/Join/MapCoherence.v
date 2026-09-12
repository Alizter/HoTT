From HoTT Require Import Basics.
Require Import Types.Paths Types.Arrow.
Require Import Homotopy.Join.Core.

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
End JoinMapCoherence.
