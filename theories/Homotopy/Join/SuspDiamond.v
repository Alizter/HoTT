From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod.
Require Import Homotopy.Join.Core Homotopy.Suspension.

Local Open Scope path_scope.

(** * Turning suspension diamonds *)

Definition diamond_susp {A : Type} (t : Susp A)
  : zigzag South t North = zigzag South t t
  := Susp_ind (fun t => zigzag South t North = zigzag South t t)
    (diamond_v South North 1) (diamond_h North South 1)
    (fun a => diamond_twist (merid a)) t.

Local Definition turn_filler_v {A B : Type} (f : A -> B)
  {a a' b : A} (p : a = b) (q : a' = b)
  {p' : f b = f a} {q' : f b = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  : turn_filler f p q p q bp bq bp bq 1
    = concat_pV p' @ (concat_pV q')^.
Proof.
  destruct p, q.
  revert p' bp q' bq.
  srapply (equiv_path_ind (fun p' => equiv_ap inverse 1 p')).
  srapply (equiv_path_ind (fun q' => equiv_ap inverse 1 q')).
  reflexivity.
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
Definition join_turn {A B C D : Type} (f : A -> D) (g : B -> C)
  : Join A B -> Join C D
  := Join_rec (joinr o f) (joinl o g)
    (fun a b => (jglue (g b) (f a))^).

Definition join_diamond_turn {A B C D : Type}
  (f : A -> D) (g : B -> C)
  {a a' : A} {b b' : B} (h : zigzag a a' b = zigzag a a' b')
  : zigzag (g b) (g b') (f a) = zigzag (g b) (g b') (f a')
  := turn_filler (join_turn f g)
    (jglue a b) (jglue a' b) (jglue a b') (jglue a' b')
    (Join_rec_beta_jglue _ _ _ a b) (Join_rec_beta_jglue _ _ _ a' b)
    (Join_rec_beta_jglue _ _ _ a b') (Join_rec_beta_jglue _ _ _ a' b') h.

(** Turning a mapped filler retains the four mapped boundary identifications. This uses naturality of the actual filler, not induction on its fixed join boundary. *)
Definition join_diamond_turn_map {A B C D E F : Type}
  (f : A -> C) (g : B -> D) (k : C -> F) (l : D -> E)
  {a a' : A} {b b' : B} {c c' : C} {d d' : D}
  (p : f a = c) (q : f a' = c') (r : g b = d) (s : g b' = d')
  (h : zigzag a a' b = zigzag a a' b')
  : join_diamond_turn k l (join_zigzag_filler f g p q r s h)
    = transport011
      (fun x : E * E => fun y : F * F =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (ap l r) (ap l s)) (path_prod' (ap k p) (ap k q))
      (join_diamond_turn (k o f) (l o g) h).
Proof.
  destruct p, q, r, s.
  lhs napply (ap (join_diamond_turn k l) (join_zigzag_filler_refl f g h)).
  unfold join_diamond_turn, turn_filler.
  napply (ap (turn_paths _ _ _ _)).
  napply (ap (fun v => (1 @@ inv_V _)^ @ v @ (1 @@ inv_V _))).
  exact (Join_rec_postcompose_filler (joinl o f) (joinr o g)
    (fun a b => jglue (f a) (g b)) (join_turn k l)
    (fun a b => (jglue (l (g b)) (k (f a)))^)
    (fun a b => Join_rec_beta_jglue _ _ _ (f a) (g b)) h).
Defined.

(** Mapping after a turn agrees with turning by the composite scalar maps. The reversed intermediate glues and their [ap_V] computations are explicit. *)
Definition join_diamond_map_turn {A B C D E F : Type}
  (f : A -> D) (g : B -> C) (k : C -> E) (l : D -> F)
  {a a' : A} {b b' : B} {c c' : E} {d d' : F}
  (p : k (g b) = c) (q : k (g b') = c')
  (r : l (f a) = d) (s : l (f a') = d')
  (h : zigzag a a' b = zigzag a a' b')
  : join_zigzag_filler k l p q r s (join_diamond_turn f g h)
    = transport011
      (fun x : E * E => fun y : F * F =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' p q) (path_prod' r s)
      (join_diamond_turn (l o f) (k o g) h).
Proof.
  destruct p, q, r, s.
  lhs napply (join_zigzag_filler_refl k l).
  lhs napply (turn_filler_map (join_turn f g) (functor_join k l)
    (jglue a b) (jglue a' b) (jglue a b') (jglue a' b')
    (Join_rec_beta_jglue _ _ _ a b) (Join_rec_beta_jglue _ _ _ a' b)
    (Join_rec_beta_jglue _ _ _ a b') (Join_rec_beta_jglue _ _ _ a' b')
    (functor_join_beta_jglue k l (g b) (f a))
    (functor_join_beta_jglue k l (g b) (f a'))
    (functor_join_beta_jglue k l (g b') (f a))
    (functor_join_beta_jglue k l (g b') (f a')) h).
  unfold join_diamond_turn, turn_filler.
  napply (ap (turn_paths _ _ _ _)).
  napply (ap (fun v => (1 @@ inv_V _)^ @ v @ (1 @@ inv_V _))).
  exact (Join_rec_postcompose_filler (joinr o f) (joinl o g)
    (fun a b => (jglue (g b) (f a))^) (functor_join k l)
    (fun a b => (jglue (k (g b)) (l (f a)))^)
    (fun a b => ap_V (functor_join k l) (jglue (g b) (f a))
      @ inverse2 (functor_join_beta_jglue k l (g b) (f a))) h).
Defined.

(** Pointwise scalar comparisons transport the entire turned filler. *)
Definition join_diamond_turn_homotopic {A B C D : Type}
  {f f' : A -> D} {g g' : B -> C} (pf : f == f') (pg : g == g')
  {a a' : A} {b b' : B} (h : zigzag a a' b = zigzag a a' b')
  : transport011
      (fun x : C * C => fun y : D * D =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (pg b) (pg b')) (path_prod' (pf a) (pf a'))
      (join_diamond_turn f g h)
    = join_diamond_turn f' g' h.
Proof.
  lhs_V napply (ap (transport011 _ _ _)
    (join_diamond_map_turn idmap idmap g f 1 1 1 1 h)).
  rhs_V napply (join_diamond_map_turn idmap idmap g' f' 1 1 1 1 h).
  exact (join_zigzag_filler_homotopic pg pf
    (join_diamond_turn idmap idmap h)).
Defined.

(** Compare a turned mapped filler with a mapped turn. All eight chosen boundary identifications, the scalar map homotopies, and the comparison with the actual target filler remain inputs. *)
Definition join_diamond_turn_compare {A B C D E F K L : Type}
  (f : A -> C) (g : B -> D) (k : C -> F) (l : D -> E)
  (u : A -> L) (v : B -> K) (f' : K -> E) (g' : L -> F)
  (pf : k o f == g' o u) (pg : l o g == f' o v)
  {a a' : A} {b b' : B} {c c' : C} {d d' : D}
  {e0 e1 : E} {f0 f1 : F}
  (p : f a = c) (q : f a' = c') (r : g b = d) (s : g b' = d')
  (p' : f' (v b) = e0) (q' : f' (v b') = e1)
  (r' : g' (u a) = f0) (s' : g' (u a') = f1)
  (h : zigzag a a' b = zigzag a a' b')
  (h' : zigzag (v b) (v b') (u a) = zigzag (v b) (v b') (u a'))
  (ht : join_diamond_turn u v h = h')
  : transport011
      (fun x : E * E => fun y : F * F =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' ((ap l r)^ @ pg b @ p') ((ap l s)^ @ pg b' @ q'))
      (path_prod' ((ap k p)^ @ pf a @ r') ((ap k q)^ @ pf a' @ s'))
      (join_diamond_turn k l (join_zigzag_filler f g p q r s h))
    = join_zigzag_filler f' g' p' q' r' s' h'.
Proof.
  destruct ht, p, q, r, s, p', q', r', s'.
  lhs napply (ap (transport011 _ _ _)
    (join_diamond_turn_map f g k l 1 1 1 1 h)).
  rhs napply (join_diamond_map_turn u v f' g' 1 1 1 1 h).
  refine (_ @ join_diamond_turn_homotopic pf pg h).
  napply (ap011 (fun p q => transport011 _ p q _));
    napply (ap011 path_prod');
    exact (concat_p1 _ @ concat_1p _).
Defined.

Definition join_diamond_turn_v {A B C D : Type}
  (f : A -> D) (g : B -> C) (a a' : A) (b : B)
  : join_diamond_turn f g (diamond_v a a' (idpath b))
    = diamond_h (f a) (f a') (idpath (g b)).
Proof.
  exact (turn_filler_v (join_turn f g) (jglue a b) (jglue a' b) _ _).
Defined.

Definition join_diamond_turn_h {A B C D : Type}
  (f : A -> D) (g : B -> C) (a : A) (b b' : B)
  : join_diamond_turn f g (diamond_h b b' (idpath a))
    = diamond_v (g b) (g b') (idpath (f a)).
Proof.
  exact (turn_filler_h (join_turn f g) (jglue a b) (jglue a b') _ _).
Defined.

(** The two pole computations are compatible with the chosen suspension twist. The eliminated path is free; no fixed join glue or diamond is eliminated. *)
Definition join_diamond_turn_twist {A B : Type} (f : A -> B)
  {n s : A} (p : n = s)
  : let Q := fun t => zigzag (f n) t (f s) = zigzag (f n) t t in
    ap01D1 (fun t => @join_diamond_turn A A B B f f s t n t)
      p (diamond_twist p) @ join_diamond_turn_h f f s n s
    = (ap (transport (fun t => Q (f t)) p) (join_diamond_turn_v f f s n n)
        @ transport_compose Q f p (diamond_h (f s) (f n) 1))
      @ moveR_transport_p Q (ap f p) _ _ (diamond_twist (ap f p)^)^.
Proof.
  destruct p.
  cbn [ap01D1 transport transport_compose ap moveR_transport_p].
  rhs napply (concat_p1 _ @@ 1).
  rhs napply (ap_idmap _ @@ 1).
  exact (turn_filler_symm (join_turn f f) (jglue n n) _).
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
    join_diamond_turn (susp_neg B o functor_susp g)
      (susp_neg B o functor_susp g) (diamond_susp t)
      = diamond_susp (susp_neg B (functor_susp g t)).
Proof.
  pose (f := susp_neg B o functor_susp g).
  pose (Q := fun t : Susp B => zigzag South t North = zigzag South t t).
  pose (turn := fun t => @join_diamond_turn
    (Susp A) (Susp A) (Susp B) (Susp B) f f South t North t).
  snapply Susp_ind.
  - exact (join_diamond_turn_v f f South North North).
  - exact (join_diamond_turn_h f f South North South).
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
