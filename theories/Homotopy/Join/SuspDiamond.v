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

(** ** Functoriality of the canonical suspension diamond *)

Local Set Universe Minimization ToSet.

Local Definition map_filler_v {A B : Type} (f : A -> B)
  {a a' b : A} (p : a = b) (q : a' = b)
  {p' : f a = f b} {q' : f a' = f b}
  (bp : ap f p = p') (bq : ap f q = q')
  : (ap_pV f p q @ (bp @@ inverse2 bq))^
      @ (ap (ap f) 1 @ (ap_pV f p q @ (bp @@ inverse2 bq))) = 1.
Proof.
  destruct bp, bq, p, q; reflexivity.
Defined.

Local Definition map_filler_h {A B : Type} (f : A -> B)
  {a b b' : A} (p : a = b) (q : a = b')
  {p' : f a = f b} {q' : f a = f b'}
  (bp : ap f p = p') (bq : ap f q = q')
  : (ap_pV f p p @ (bp @@ inverse2 bp))^
      @ (ap (ap f) (concat_pV p @ (concat_pV q)^)
        @ (ap_pV f q q @ (bq @@ inverse2 bq)))
    = concat_pV p' @ (concat_pV q')^.
Proof.
  destruct bp, bq, p, q; reflexivity.
Defined.

Local Definition map_filler_symm {A B : Type} (f : A -> B)
  {a b : A} (p : a = b) {q : f a = f b} (bp : ap f p = q)
  : ap (fun h => (ap_pV f p p @ (bp @@ inverse2 bp))^
      @ (ap (ap f) h @ (ap_pV f p p @ (bp @@ inverse2 bp))))
      (concat_pV (concat_pV p))^ @ map_filler_h f p p bp bp
    = map_filler_v f p p bp bp @ (concat_pV (concat_pV q))^.
Proof.
  destruct bp, p; reflexivity.
Defined.

Definition join_diamond_map_v {A B C D : Type}
  (f : A -> C) (g : B -> D) (a a' : A) (b : B)
  : (Join_rec_beta_zigzag _ _
        (fun x y => jglue (f x) (g y)) a a' b)^
      @ (ap (ap (functor_join f g)) (diamond_v a a' (idpath b))
        @ Join_rec_beta_zigzag _ _
          (fun x y => jglue (f x) (g y)) a a' b)
    = diamond_v (f a) (f a') (idpath (g b)).
Proof.
  exact (map_filler_v (functor_join f g)
    (jglue a b) (jglue a' b) _ _).
Defined.

Definition join_diamond_map_h {A B C D : Type}
  (f : A -> C) (g : B -> D) (a : A) (b b' : B)
  : (Join_rec_beta_zigzag _ _
        (fun x y => jglue (f x) (g y)) a a b)^
      @ (ap (ap (functor_join f g)) (diamond_h b b' (idpath a))
        @ Join_rec_beta_zigzag _ _
          (fun x y => jglue (f x) (g y)) a a b')
    = diamond_h (g b) (g b') (idpath (f a)).
Proof.
  exact (map_filler_h (functor_join f g)
    (jglue a b) (jglue a b') _ _).
Defined.

(** Mapping preserves the chosen twist between the vertical and horizontal diamonds. The path [p] and all its endpoints are free; no fixed join loop is eliminated. *)
Definition join_diamond_map_twist {A B : Type} (f : A -> B)
  {n s : A} (p : n = s)
  : let Q := fun t : B => zigzag (f s) t (f n) = zigzag (f s) t t in
    let m := fun (t : A) (h : zigzag s t n = zigzag s t t) =>
      (Join_rec_beta_zigzag _ _
          (fun x y => jglue (f x) (f y)) s t n)^
        @ (ap (ap (functor_join f f)) h
          @ Join_rec_beta_zigzag _ _
            (fun x y => jglue (f x) (f y)) s t t) in
    ap01D1 m p (diamond_twist p) @ join_diamond_map_h f f s n s
    = (ap (transport (fun t => Q (f t)) p)
        (join_diamond_map_v f f s n n)
        @ transport_compose Q f p (diamond_v (f s) (f n) 1))
      @ diamond_twist (ap f p).
Proof.
  destruct p; cbn [ap01D1 transport transport_compose ap].
  rhs napply (concat_p1 _ @@ 1).
  rhs napply (ap_idmap _ @@ 1).
  exact (map_filler_symm (functor_join f f) (jglue n n) _).
Defined.

(** In particular this applies to suspension conjugation, without any involution, multiplication, truncation, or extensionality hypothesis. The comparison is with [diamond_susp] itself, not an unspecified filler with the same vertices. *)
Definition diamond_susp_functor@{i j|}
  {A : Type@{i}} {B : Type@{j}} (g : A -> B)
  : forall t : Susp A,
    join_zigzag_filler (functor_susp g) (functor_susp g)
      1 1 1 1 (diamond_susp t)
    = diamond_susp (functor_susp g t).
Proof.
  intro t.
  lhs napply (join_zigzag_filler_refl
    (functor_susp g) (functor_susp g)).
  revert t.
  pose (f := functor_susp g).
  pose (Q := fun t : Susp B => zigzag South t North = zigzag South t t).
  pose (m := fun (t : Susp A)
    (h : zigzag South t North = zigzag South t t) =>
    (Join_rec_beta_zigzag _ _
        (fun x y => jglue (f x) (f y)) South t North)^
      @ (ap (ap (functor_join f f)) h
        @ Join_rec_beta_zigzag _ _
          (fun x y => jglue (f x) (f y)) South t t)).
  snapply Susp_ind.
  - exact (join_diamond_map_v f f South North North).
  - exact (join_diamond_map_h f f South North South).
  - intro a.
    assert (E : forall (q : North = South :> Susp B),
      q = merid (g a) -> apD diamond_susp q = diamond_twist q).
    { snapply paths_ind_r.
      exact (Susp_ind_beta_merid _ _ _ _ (g a)). }
    lhs napply (transport_paths_FlFr_D
      (f:=fun t => m t (diamond_susp t))
      (g:=fun t => diamond_susp (f t)) (merid a) _).
    lhs napply concat_pp_p.
    apply moveR_Vp; symmetry.
    lhs napply (apD_composeD m diamond_susp (merid a) @@ 1).
    lhs napply (ap (ap01D1 m (merid a))
      (Susp_ind_beta_merid _ _ _ _ a) @@ 1).
    rhs napply (1 @@ apD_compose f diamond_susp (merid a)).
    rhs napply (1 @@ (1 @@ E (ap f (merid a))
      (functor_susp_beta_merid@{i j i} g a))).
    rhs napply concat_p_pp.
    exact (join_diamond_map_twist f (merid a)).
Defined.

(** ** Reversing both pairs of vertices *)

Definition join_diamond_rotate {A B : Type}
  {a a' : A} {b b' : B}
  (h : zigzag a a' b = zigzag a a' b')
  : zigzag a' a b' = zigzag a' a b
  := (inv_pV (jglue a b') (jglue a' b'))^
    @ inverse2 h^ @ inv_pV (jglue a b) (jglue a' b).

Definition join_diamond_rotate_v {A B : Type} (a a' : A) (b : B)
  : join_diamond_rotate (diamond_v a a' (idpath b)) = 1.
Proof.
  unfold join_diamond_rotate; cbn [diamond_v inverse2 ap inverse].
  lhs napply (concat_p1 _ @@ 1).
  apply concat_Vp.
Defined.

Definition join_diamond_rotate_h {A B : Type} (a : A) (b b' : B)
  : join_diamond_rotate (diamond_h b b' (idpath a))
    = diamond_h b' b (idpath a).
Proof.
  unfold join_diamond_rotate; cbn [diamond_h]; unfold zigzag.
  generalize (jglue a b), (jglue a b').
  generalize (joinr (A:=A) b), (joinr (A:=A) b').
  intros y z p q; destruct p, q; reflexivity.
Defined.

Definition join_zigzag_filler_v {A B C D : Type}
  (f : A -> C) (g : B -> D) (a a' : A) (b : B)
  {c c' : C} {d : D}
  (p : f a = c) (q : f a' = c') (r : g b = d)
  : join_zigzag_filler f g p q r r (diamond_v a a' 1) = 1.
Proof.
  destruct p, q, r.
  lhs napply (join_zigzag_filler_refl f g _).
  apply join_diamond_map_v.
Defined.

Definition join_zigzag_filler_h {A B C D : Type}
  (f : A -> C) (g : B -> D) (a : A) (b b' : B)
  {c : C} {d d' : D}
  (p : f a = c) (r : g b = d) (s : g b' = d')
  : join_zigzag_filler f g p p r s (diamond_h b b' 1)
    = diamond_h d d' (idpath c).
Proof.
  destruct p, r, s.
  lhs napply (join_zigzag_filler_refl f g _).
  apply join_diamond_map_h.
Defined.

(** The two degenerate computations retain their compatibility at the common corner. *)
Definition join_zigzag_filler_symm {A B C D : Type}
  (f : A -> C) (g : B -> D) (a : A) (b : B)
  {c : C} {d : D} (p : f a = c) (r : g b = d)
  : ap (join_zigzag_filler f g p p r r) (diamond_symm a b)
      @ join_zigzag_filler_h f g a b b p r r
    = join_zigzag_filler_v f g a a b p p r @ diamond_symm c d.
Proof.
  destruct p, r.
  change (ap (join_zigzag_filler f g 1 1 1 1) (diamond_symm a b)
      @ (join_zigzag_filler_refl f g _ @ join_diamond_map_h f g a b b)
    = (join_zigzag_filler_refl f g _ @ join_diamond_map_v f g a a b)
      @ diamond_symm (f a) (g b)).
  lhs napply concat_p_pp.
  lhs napply (concat_Ap (join_zigzag_filler_refl f g) (diamond_symm a b) @@ 1).
  lhs napply concat_pp_p.
  rhs napply concat_pp_p.
  napply (ap (concat (join_zigzag_filler_refl f g _))).
  exact (map_filler_symm (functor_join f g) (jglue a b) _).
Defined.

Definition join_diamond_rotate_symm {A B : Type} (a : A) (b : B)
  : ap join_diamond_rotate (diamond_symm a b)
      @ join_diamond_rotate_h a b b
    = join_diamond_rotate_v a a b @ diamond_symm a b.
Proof.
  unfold join_diamond_rotate_v, join_diamond_rotate_h,
    join_diamond_rotate, diamond_symm.
  unfold diamond_h, diamond_v, zigzag.
  cbn [ap].
  generalize (jglue a b); generalize (joinr (A:=A) b).
  intros z p; destruct p; reflexivity.
Defined.

Definition join_zigzag_filler_rotate_v {A B C D : Type}
  (f : A -> C) (g : B -> D) (a a' : A) (b : B)
  {c c' : C} {d : D}
  (p : f a = c) (q : f a' = c') (r s : g b = d) (e : r = s)
  : join_zigzag_filler f g p q r s (diamond_v a a' 1)
    = join_diamond_rotate (diamond_v c' c (idpath d))
  := ap (fun s => join_zigzag_filler f g p q r s (diamond_v a a' 1)) e^
    @ (join_zigzag_filler_v f g a a' b p q r
      @ (join_diamond_rotate_v c' c d)^).

Definition join_zigzag_filler_rotate_h {A B C D : Type}
  (f : A -> C) (g : B -> D) (a : A) (b b' : B)
  {c : C} {d d' : D}
  (p q : f a = c) (r : g b = d) (s : g b' = d') (e : p = q)
  : join_zigzag_filler f g p q r s (diamond_h b b' 1)
    = join_diamond_rotate (diamond_h d' d (idpath c))
  := ap (fun q => join_zigzag_filler f g p q r s (diamond_h b b' 1)) e^
    @ (join_zigzag_filler_h f g a b b' p r s
      @ (join_diamond_rotate_h c d' d)^).

Definition join_zigzag_filler_rotate_symm {A B C D : Type}
  (f : A -> C) (g : B -> D) (a : A) (b : B)
  {c : C} {d : D} (p q : f a = c) (r s : g b = d)
  (e0 : r = s) (e1 : p = q)
  : ap (join_zigzag_filler f g p q r s) (diamond_symm a b)
      @ join_zigzag_filler_rotate_h f g a b b p q r s e1
    = join_zigzag_filler_rotate_v f g a a b p q r s e0
      @ ap join_diamond_rotate (diamond_symm c d).
Proof.
  destruct e0, e1.
  unfold join_zigzag_filler_rotate_h, join_zigzag_filler_rotate_v.
  cbn [ap inverse].
  lhs napply (1 @@ concat_1p _).
  rhs napply (concat_1p _ @@ 1).
  lhs napply concat_p_pp.
  lhs napply (join_zigzag_filler_symm f g a b p r @@ 1).
  lhs napply concat_pp_p.
  rhs napply concat_pp_p.
  napply (ap (concat (join_zigzag_filler_v f g a a b p p r))).
  apply moveL_Vp.
  lhs napply concat_p_pp.
  apply moveR_pV.
  symmetry; apply join_diamond_rotate_symm.
Defined.

(** A parameter-dependent pair of scalar maps can reverse both vertex pairs. Its two degenerate comparisons commute with the actual twist, including the chosen boundary identifications. Only the free parameter path is eliminated. *)
Definition join_zigzag_filler_rotate_twist
  {I A B : Type} {i0 i1 : I} (p : i0 = i1)
  (t : I -> A) (v : I -> B) (f g : I -> A -> B)
  (b00 : forall i, f i (t i1) = v i)
  (b01 : forall i, f i (t i) = v i1)
  (b10 : forall i, g i (t i0) = v i)
  (b11 : forall i, g i (t i) = v i0)
  (e0 : b10 i0 = b11 i0) (e1 : b00 i1 = b01 i1)
  : let QA := fun a => zigzag (t i1) a (t i0) = zigzag (t i1) a a in
    let QB := fun b => zigzag (v i1) b (v i0) = zigzag (v i1) b b in
    let m := fun i (h : QA (t i)) =>
      join_zigzag_filler (f i) (g i) (b00 i) (b01 i) (b10 i) (b11 i) h in
    let rot := fun i (h : QB (v i)) => join_diamond_rotate h in
    ap01D1 m p
        (transport_compose QA t p (diamond_v (t i1) (t i0) 1)
          @ diamond_twist (ap t p))
      @ join_zigzag_filler_rotate_h (f i1) (g i1)
        (t i1) (t i0) (t i1) (b00 i1) (b01 i1) (b10 i1) (b11 i1) e1
    = ap (transport (fun i => zigzag (v i) (v i1) (v i)
        = zigzag (v i) (v i1) (v i0)) p)
        (join_zigzag_filler_rotate_v (f i0) (g i0)
          (t i1) (t i0) (t i0) (b00 i0) (b01 i0) (b10 i0) (b11 i0) e0)
      @ ap01D1 rot p
        (transport_compose QB v p (diamond_v (v i1) (v i0) 1)
          @ diamond_twist (ap v p)).
Proof.
  destruct p.
  cbn [ap01D1 ap transport_compose].
  change (ap (join_zigzag_filler (f i0) (g i0)
      (b00 i0) (b01 i0) (b10 i0) (b11 i0))
      (1 @ diamond_symm (t i0) (t i0))
      @ join_zigzag_filler_rotate_h (f i0) (g i0) (t i0) (t i0) (t i0)
        (b00 i0) (b01 i0) (b10 i0) (b11 i0) e1
    = ap idmap (join_zigzag_filler_rotate_v (f i0) (g i0)
        (t i0) (t i0) (t i0) (b00 i0) (b01 i0) (b10 i0) (b11 i0) e0)
      @ ap join_diamond_rotate (1 @ diamond_symm (v i0) (v i0))).
  lhs napply (ap (ap (join_zigzag_filler (f i0) (g i0)
    (b00 i0) (b01 i0) (b10 i0) (b11 i0))) (concat_1p _) @@ 1).
  rhs napply (ap_idmap _ @@ ap (ap join_diamond_rotate) (concat_1p _)).
  apply join_zigzag_filler_rotate_symm.
Defined.

Local Definition map_filler_rotate {A B : Type} (f : A -> B)
  {x y z w : A}
  (p : x = y) (q : z = y) (r : x = w) (s : z = w)
  {p' : f x = f y} {q' : f z = f y}
  {r' : f x = f w} {s' : f z = f w}
  (bp : ap f p = p') (bq : ap f q = q')
  (br : ap f r = r') (bs : ap f s = s')
  (h : p @ q^ = r @ s^)
  : (inv_pV r' s')^
      @ inverse2 ((ap_pV f p q @ (bp @@ inverse2 bq))^
        @ (ap (ap f) h @ (ap_pV f r s @ (br @@ inverse2 bs))))^
      @ inv_pV p' q'
    = (ap_pV f s r @ (bs @@ inverse2 br))^
      @ (ap (ap f) ((inv_pV r s)^ @ inverse2 h^ @ inv_pV p q)
        @ (ap_pV f q p @ (bq @@ inverse2 bp))).
Proof.
  destruct bp, bq, br, bs, p, q, r.
  revert s h.
  srapply (equiv_path_ind (fun s =>
    equiv_ap (fun q => 1 @ q^) 1 s)).
  reflexivity.
Defined.

(** Rotation commutes with mapping the actual filler, reversing the order of all four selected boundary identifications. *)
Definition join_diamond_rotate_map {A B C D : Type}
  (f : A -> C) (g : B -> D)
  {a a' : A} {b b' : B} {c c' : C} {d d' : D}
  (p : f a = c) (q : f a' = c') (r : g b = d) (s : g b' = d')
  (h : zigzag a a' b = zigzag a a' b')
  : join_diamond_rotate (join_zigzag_filler f g p q r s h)
    = join_zigzag_filler f g q p s r (join_diamond_rotate h).
Proof.
  destruct p, q, r, s.
  lhs napply (ap join_diamond_rotate (join_zigzag_filler_refl f g h)).
  rhs napply (join_zigzag_filler_refl f g (join_diamond_rotate h)).
  exact (map_filler_rotate (functor_join f g)
    (jglue a b) (jglue a' b) (jglue a b') (jglue a' b') _ _ _ _ h).
Defined.

(** Transport a mapped rotation using the actual scalar map homotopies and all the boundary paths. *)
Definition join_diamond_rotate_compare {A B C D E F : Type}
  (f : A -> E) (g : B -> F) (l : C -> A) (r : D -> B)
  (f' : C -> E) (g' : D -> F)
  (pf : f o l == f') (pg : g o r == g')
  {a a' : A} {b b' : B} {c c' : C} {d d' : D}
  {x x' z z' : E} {y y' w w' : F}
  (e00 : l c = a') (e10 : l c' = a)
  (e01 : r d = b') (e11 : r d' = b)
  (p : f a = x) (q : f a' = x') (s : g b = y) (t : g b' = y')
  (p' : f' c = z) (q' : f' c' = z')
  (s' : g' d = w) (t' : g' d' = w')
  (h : zigzag a a' b = zigzag a a' b')
  (h' : zigzag c c' d = zigzag c c' d')
  (ht : join_zigzag_filler l r e00 e10 e01 e11 h'
    = join_diamond_rotate h)
  : transport011
      (fun x : E * E => fun y : F * F =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (q^ @ (ap f e00)^ @ pf c @ p')
        (p^ @ (ap f e10)^ @ pf c' @ q'))
      (path_prod' (t^ @ (ap g e01)^ @ pg d @ s')
        (s^ @ (ap g e11)^ @ pg d' @ t'))
      (join_diamond_rotate (join_zigzag_filler f g p q s t h))
    = join_zigzag_filler f' g' p' q' s' t' h'.
Proof.
  destruct e00, e10, e01, e11, p, q, s, t, p', q', s', t'.
  pose (Q := fun (x : E * E) (y : F * F) =>
    zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y)).
  pose (px := path_prod' ((1 @ pf c) @ 1) ((1 @ pf c') @ 1)).
  pose (py := path_prod' ((1 @ pg d) @ 1) ((1 @ pg d') @ 1)).
  lhs napply (ap (transport011 Q px py)
    (join_diamond_rotate_map f g 1 1 1 1 h)).
  lhs napply (ap (fun h => transport011 Q px py
    (join_zigzag_filler f g 1 1 1 1 h)) ht^).
  lhs napply (ap (transport011 Q px py)
    (join_zigzag_filler_compose l r f g 1 1 1 1 h')).
  refine (_ @ join_zigzag_filler_homotopic pf pg h').
  napply (ap011 (fun p q => transport011 Q p q _));
    napply (ap011 path_prod');
    exact (concat_p1 _ @ concat_1p _).
Defined.

(** A rotated filler comparison supplies the mixed cube with one input direction reversed on each side. The four side faces use the specified scalar paths. *)
Definition join_zigzag_filler_cube_rotate {A B : Type}
  {a a' c c' : A} {b b' d d' : B}
  (p : a' = c) (q : a = c') (r : b = d) (s : b' = d')
  (h : zigzag a a' b = zigzag a a' b')
  (k : zigzag c c' d' = zigzag c c' d)
  (v : transport011
    (fun x : A * A => fun y : B * B =>
      zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
    (path_prod' p q) (path_prod' r s) (join_diamond_rotate h^) = k^)
  : let cf := (1 @@ inv_V (jglue a' b))^
      @ (inverse_natural (jglue a b) (jglue a' b')^ h)^ in
    let cg := inverse_natural (jglue c d) (jglue c' d')^ k^
      @ (1 @@ inv_V (jglue c' d)) in
    concat_natural (jglue a' b')^ (jglue a b) (jglue c' d)
      (jglue a b')^ (jglue a' b) (ap joinl q) (ap joinr r)
      cf (join_natsq q r)^
      @ (inverse_natural _ _ (join_natsq q s) @@ 1)
    = (1 @@ (join_natsq p r)^)
      @ concat_natural (jglue a' b')^ (jglue c d')^ (jglue c' d)
        (ap joinr s) (ap joinl p) (jglue c' d')^ (jglue c d)
        (inverse_natural _ _ (join_natsq p s)) cg.
Proof.
  destruct p, q, r, s.
  rhs_V napply (1 @@ ap (concat_natural _ _ _ _ _ _ _ _)
    (inverse_naturality_rotation
      (jglue a b) (jglue a' b) (jglue a b') (jglue a' b') h
      @ ap (fun k => inverse_natural (jglue a' b) (jglue a b')^ k
        @ (1 @@ inv_V (jglue a b))) v)).
  exact (concat_pV_cube_unit_inverse
    (jglue a b) (jglue a' b) (jglue a b') (jglue a' b') h).
Defined.
