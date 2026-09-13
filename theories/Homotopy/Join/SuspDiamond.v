From HoTT Require Import Basics.
Require Import Types.Paths.
Require Import Homotopy.Join.Core Homotopy.Suspension.

Local Open Scope path_scope.

(** * Turning suspension diamonds *)

Definition diamond_susp {A : Type} (t : Susp A)
  : zigzag South t North = zigzag South t t
  := Susp_ind (fun t => zigzag South t North = zigzag South t t)
    (diamond_v South North 1) (diamond_h North South 1)
    (fun a => diamond_twist (merid a)) t.

Local Definition turn_paths {A : Type} {a a' b b' : A}
  (p : a = b) (q : a = b') (r : a' = b) (s : a' = b')
  (h : p^ @ q = r^ @ s) : p @ r^ = q @ s^.
Proof.
  apply moveL_pV.
  lhs napply concat_pp_p.
  lhs_V napply (1 @@ h).
  apply concat_p_Vp.
Defined.

Local Definition turn_beta {A B : Type} (f : A -> B)
  {a a' b : A} (p : a = b) (q : a' = b)
  {p' : f b = f a} {q' : f b = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  : ap f (p @ q^) = p'^ @ q'
  := ap_pV f p q @ (bp @@ (inverse2 bq @ inv_V q')).

Local Definition turn_filler {A B : Type} (f : A -> B)
  {a a' b b' : A}
  (p : a = b) (q : a' = b) (r : a = b') (s : a' = b')
  {p' : f b = f a} {q' : f b = f a'}
  {r' : f b' = f a} {s' : f b' = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  (br : ap f r = r'^) (bs : ap f s = s'^)
  (h : p @ q^ = r @ s^)
  : p' @ r'^ = q' @ s'^
  := turn_paths p' q' r' s'
    ((turn_beta f p q bp bq)^ @ ap (ap f) h @ turn_beta f r s br bs).

Local Definition turn_paths_refl {A : Type} {a b b' : A}
  (p : a = b) (q : a = b')
  : turn_paths p q p q 1 = concat_pV p @ (concat_pV q)^.
Proof.
  destruct p, q; reflexivity.
Defined.

Local Definition turn_filler_v {A B : Type} (f : A -> B)
  {a a' b : A} (p : a = b) (q : a' = b)
  {p' : f b = f a} {q' : f b = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  : turn_filler f p q p q bp bq bp bq 1
    = concat_pV p' @ (concat_pV q')^.
Proof.
  unfold turn_filler.
  refine (ap (turn_paths p' q' p' q') _ @ turn_paths_refl p' q').
  lhs napply (concat_p1 _ @@ 1).
  apply concat_Vp.
Defined.

Local Definition turn_filler_h {A B : Type} (f : A -> B)
  {a b b' : A} (p : a = b) (q : a = b')
  {p' : f b = f a} {q' : f b' = f a}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  : turn_filler f p p q q bp bp bq bq
      (concat_pV p @ (concat_pV q)^) = 1.
Proof.
  destruct p, q.
  revert p' bp q' bq.
  srapply (equiv_path_ind (fun p' => equiv_ap inverse 1 p')).
  srapply (equiv_path_ind (fun q' => equiv_ap inverse 1 q')).
  reflexivity.
Defined.

Local Definition turn_filler_symm {A B : Type} (f : A -> B)
  {a b : A} (p : a = b) {q : f b = f a} (bp : ap f p = q^)
  : ap (turn_filler f p p p p bp bp bp bp)
      (concat_pV (concat_pV p))^ @ turn_filler_h f p p bp bp
    = turn_filler_v f p p bp bp @ ((concat_pV (concat_pV q))^)^.
Proof.
  destruct p; revert q bp.
  srapply (equiv_path_ind (fun q => equiv_ap inverse 1 q)).
  reflexivity.
Defined.

(** The turn exchanges the two join factors while applying the scalar map. *)
Definition join_turn {A B : Type} (f : A -> B) : Join A A -> Join B B
  := Join_rec (joinr o f) (joinl o f)
    (fun a b => (jglue (f b) (f a))^).

Definition join_diamond_turn {A B : Type} (f : A -> B)
  {a a' b b' : A} (h : zigzag a a' b = zigzag a a' b')
  : zigzag (f b) (f b') (f a) = zigzag (f b) (f b') (f a')
  := turn_filler (join_turn f)
    (jglue a b) (jglue a' b) (jglue a b') (jglue a' b')
    (Join_rec_beta_jglue _ _ _ a b) (Join_rec_beta_jglue _ _ _ a' b)
    (Join_rec_beta_jglue _ _ _ a b') (Join_rec_beta_jglue _ _ _ a' b') h.

Definition join_diamond_turn_v {A B : Type} (f : A -> B) (a a' b : A)
  : join_diamond_turn f (diamond_v a a' (idpath b))
    = diamond_h (f a) (f a') (idpath (f b)).
Proof.
  exact (turn_filler_v (join_turn f) (jglue a b) (jglue a' b) _ _).
Defined.

Definition join_diamond_turn_h {A B : Type} (f : A -> B) (a b b' : A)
  : join_diamond_turn f (diamond_h b b' (idpath a))
    = diamond_v (f b) (f b') (idpath (f a)).
Proof.
  exact (turn_filler_h (join_turn f) (jglue a b) (jglue a b') _ _).
Defined.

(** The two pole computations are compatible with the chosen suspension twist. The eliminated path is free; no fixed join glue or diamond is eliminated. *)
Definition join_diamond_turn_twist {A B : Type} (f : A -> B)
  {n s : A} (p : n = s)
  : let Q := fun t => zigzag (f n) t (f s) = zigzag (f n) t t in
    ap01D1 (fun t => @join_diamond_turn A B f s t n t)
      p (diamond_twist p) @ join_diamond_turn_h f s n s
    = (ap (transport (fun t => Q (f t)) p) (join_diamond_turn_v f s n n)
        @ transport_compose Q f p (diamond_h (f s) (f n) 1))
      @ moveR_transport_p Q (ap f p) _ _ (diamond_twist (ap f p)^)^.
Proof.
  destruct p.
  cbn [ap01D1 transport transport_compose ap moveR_transport_p].
  rhs napply (concat_p1 _ @@ 1).
  rhs napply (ap_idmap _ @@ 1).
  exact (turn_filler_symm (join_turn f) (jglue n n) _).
Defined.

Local Definition diamond_twist_inverse {A : Type} {n s : A} (p : n = s)
  : let Q := fun t => zigzag s t n = zigzag s t t in
    moveR_transport_V Q p _ _ (diamond_twist p)^
    = moveR_transport_p Q p^ _ _ (diamond_twist (p^)^)^.
Proof.
  destruct p; reflexivity.
Defined.

(** Negating a suspension reverses the pole computations as well as the meridians. The chosen turn respects both, not just the four vertices. *)
Definition diamond_susp_turn {A B : Type} (g : A -> B)
  : forall t : Susp A,
    join_diamond_turn (susp_neg B o functor_susp g) (diamond_susp t)
      = diamond_susp (susp_neg B (functor_susp g t)).
Proof.
  pose (f := susp_neg B o functor_susp g).
  pose (Q := fun t : Susp B => zigzag South t North = zigzag South t t).
  pose (turn := fun t => @join_diamond_turn (Susp A) (Susp B)
    f South t North t).
  snapply Susp_ind.
  - exact (join_diamond_turn_v f South North North).
  - exact (join_diamond_turn_h f South North South).
  - intro a.
    assert (E : forall (q : South = North :> Susp B),
      q = (merid (g a))^ ->
      apD diamond_susp q
        = moveR_transport_p Q q _ _ (diamond_twist q^)^).
    { snapply paths_ind_r.
      lhs napply (apD_V diamond_susp (merid (g a))).
      lhs napply (ap (fun h => moveR_transport_V Q (merid (g a)) _ _ h^)
        (Susp_ind_beta_merid _ _ _ _ (g a))).
      exact (diamond_twist_inverse (merid (g a))). }
    assert (bf : ap f (merid a) = (merid (g a))^).
    { refine (ap_compose (functor_susp g) (susp_neg B) (merid a) @ _).
      refine (ap (ap (susp_neg B)) (functor_susp_beta_merid g a) @ _).
      exact (Susp_rec_beta_merid (g a)). }
    lhs napply (transport_paths_FlFr_D
      (f:=fun t => turn t (diamond_susp t))
      (g:=fun t => diamond_susp (f t)) (merid a) _).
    lhs napply concat_pp_p.
    apply moveR_Vp; symmetry.
    lhs napply (apD_composeD turn diamond_susp (merid a) @@ 1).
    lhs napply (ap (ap01D1 turn (merid a))
      (Susp_ind_beta_merid _ _ _ _ a) @@ 1).
    rhs napply (1 @@ apD_compose f diamond_susp (merid a)).
    rhs napply (1 @@ (1 @@ E (ap f (merid a)) bf)).
    rhs napply concat_p_pp.
    exact (join_diamond_turn_twist f (merid a)).
Defined.
