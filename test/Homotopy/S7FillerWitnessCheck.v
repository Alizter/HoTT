From HoTT Require Import Basics Types.
From HoTT Require Import Homotopy.Join.Core.
Local Open Scope path_scope.

Section HomotopyUnitChecks.
  Context {A B C D : Type} (f : A -> C) (g : B -> D).

  Example filler_homotopy_refl_left (a : A)
    : join_zigzag_filler_homotopy_refl f g (joinl a) = 1 := idpath.

  Example filler_homotopy_refl_right (b : B)
    : join_zigzag_filler_homotopy_refl f g (joinr b) = 1 := idpath.
End HomotopyUnitChecks.

(** The extraction never assumes truncation of the fiber, even when the two base paths and their comparison are identities. *)
Example fiber_square_constant {T : Type} {u v : T} (r s : u = v)
  (w : path_sigma' (fun _ : Unit => T) (idpath tt) r
    = path_sigma' (fun _ : Unit => T) (idpath tt) s)
  : r = s
  := path_sigma_fiber_square (fun _ : Unit => T) (idpath (idpath tt)) r s w.

(** The identity computation holds for the entire chosen filler comparison, not just its underlying pointwise join homotopy. *)
Example identity_filler_comparison {A B C D : Type}
  (f : A -> C) (g : B -> D) {a a' : A} {b b' : B}
  (h : zigzag a a' b = zigzag a a' b')
  : join_zigzag_filler_homotopic (fun a => idpath (f a))
      (fun b => idpath (g b)) h = 1
  := join_zigzag_filler_homotopic_refl f g h.

Example identity_complete_change {X C D : Type} {n e : X}
  (h : forall t, zigzag n t t = zigzag n t e)
  (f : X -> C) (g : X -> D) (t : X)
  {c c' : C} {d d' : D}
  (p : f n = c) (q : f t = c') (r : g t = d) (s : g e = d')
  : join_zigzag_filler_change_path h (fun x => idpath (f x))
      (fun x => idpath (g x)) 1 p q r s p q r s = 1
  := join_zigzag_filler_change_path_refl h f g t p q r s.

(** The parameter computation retains arbitrary corners and an explicitly supplied pole computation; neither the fibers nor their path spaces are assumed truncated. *)
Section ParameterUnitUniverses.
  Universes i j k l m.
  Context {X : Type@{i}} {C : Type@{k}} {D : Type@{l}} {n e : X}.

  Example parameter_unit_keeps_boundaries
    (h : forall t, zigzag@{i i j} n t t = zigzag n t e)
    (he : h e = 1) (f : X -> C) (g : X -> D)
    {t : X} (p_t : t = e) {c c' : C} {d d' : D}
    (p : f n = c) (q : f t = c') (r : g t = d) (s : g e = d')
    : join_zigzag_filler@{i i k l m j} f g p q r s (h t)
      = diamond_v@{k l m} c c' (r^ @ ap g p_t @ s)
    := join_zigzag_filler_parameter_unit@{i k l j m} h he f g p_t p q r s.
End ParameterUnitUniverses.

(** Reversing the actual cube conversion recovers arbitrary supplied fillers and comparisons. The join and its two input types retain independent universes. *)
Section FillerCubeEquivalence.
  Universes i j k.
  Context {A : Type@{i}} {B : Type@{j}}
    {a a' c c' : A} {b b' d d' : B}
    (p : a = c) (q : a' = c') (r : b = d) (s : b' = d')
    (h : zigzag@{i j k} a a' b = zigzag a a' b')
    (h' : zigzag@{i j k} c c' d = zigzag c c' d').
  Let Input := transport011
    (fun x : A * A => fun y : B * B =>
      zigzag@{i j k} (fst x) (snd x) (fst y)
        = zigzag (fst x) (snd x) (snd y))
    (path_prod' p q) (path_prod' r s) h = h'.
  Let convert := join_zigzag_filler_cube@{i j k} p q r s h h'.
  Let E := Build_Equiv _ _ convert
    (isequiv_join_zigzag_filler_cube@{i j k} p q r s h h').

  Example filler_cube_forward (v : Input) : E v = convert v := idpath.
  Example filler_cube_roundtrip (v : Input)
    : E^-1 (convert v) = v := eissect E v.
  Example filler_cube_comparison_roundtrip {v w : Input} (q : v = w)
    : (equiv_ap E v w)^-1 (ap convert q) = q
    := eissect (equiv_ap E v w) q.
End FillerCubeEquivalence.

(** The proof before exposing its recursor homotopy and zigzag computation. *)
Definition legacy_filler_homotopic {A B C D : Type}
  {f f' : A -> C} {g g' : B -> D} (pf : f == f') (pg : g == g')
  {a a' : A} {b b' : B} (h : zigzag a a' b = zigzag a a' b')
  : transport011
      (fun x : C * C => fun y : D * D =>
        zigzag (fst x) (snd x) (fst y) = zigzag (fst x) (snd x) (snd y))
      (path_prod' (pf a) (pf a')) (path_prod' (pg b) (pg b'))
      (join_zigzag_filler f g 1 1 1 1 h)
    = join_zigzag_filler f' g' 1 1 1 1 h.
Proof.
  pose (F := functor_join f g).
  pose (G := functor_join f' g').
  pose (bF := functor_join_beta_jglue f g).
  pose (bG := functor_join_beta_jglue f' g').
  pose (zF := functor_join_beta_zigzag f g).
  pose (zG := functor_join_beta_zigzag f' g').
  pose (hc := fun u v => ((bF u v @@ 1) @ (join_natsq (pf u) (pg v))^)
    @ (1 @@ bG u v)^).
  pose (K := Join_ind_FlFr F G
    (fun u => ap joinl (pf u)) (fun v => ap joinr (pg v)) hc).
  assert (betaK : forall v, concat_Ap K (zigzag a a' v)
    = ((zF a a' v @@ 1) @ (zigzag_natsq (pf a) (pf a') (pg v))^)
      @ (1 @@ zG a a' v)^).
  { intro v.
    lhs napply concat_Ap_pV.
    lhs napply ((1 @@ ap011 (concat_pV_natural _ _ _)
      (Join_ind_FlFr_beta_jglue F G _ _ hc a v)
      (Join_ind_FlFr_beta_jglue F G _ _ hc a' v)) @@ 1).
    lhs napply ((1 @@ concat_pV_natural_change _ _ _ _ _ _ _ _ _) @@ 1).
    lhs napply naturality_change_compose.
    exact ((1 @@ zigzag_natsq_pV (pf a) (pf a') (pg v)) @@ 1). }
  assert (betaN : forall v,
    ((concat_Ap K (zigzag a a' v))^
      @ ap (fun q => q @ K (joinl a')) (zF a a' v))
      @ (zigzag_natsq (pf a) (pf a') (pg v))^
    = ap (fun q => K (joinl a) @ q) (zG a a' v)).
  { intro v.
    lhs napply concat_pp_p.
    apply moveR_Vp, moveL_pM.
    exact (betaK v)^. }
  lhs napply (ap (transport011 _ (path_prod' (pf a) (pf a'))
    (path_prod' (pg b) (pg b'))) (join_zigzag_filler_refl f g h)).
  rhs napply (join_zigzag_filler_refl f' g' h).
  lhs napply (transport_zigzag_filler (pf a) (pf a') (pg b) (pg b')).
  rhs_V napply (whiskerL_VpL (K (joinl a))
    ((zG a a' b)^ @ (ap (ap G) h @ zG a a' b'))).
  napply (ap (cancelL (K (joinl a)) _ _)).
  lhs napply concat_pp_p.
  lhs_V napply (inv_V (zigzag_natsq (pf a) (pf a') (pg b)) @@ 1).
  rhs napply (ap_path_image (ap G) (fun q => K (joinl a) @ q)
    (zG a a' b) (zG a a' b') h).
  exact (ap_path_image_natural
    (fun p : joinl a = joinl a' => ap F p)
    (fun q => q @ K (joinl a'))
    (fun p : joinl a = joinl a' => K (joinl a) @ ap G p)
    (fun p => (concat_Ap K p)^)
    (zF a a' b) (zF a a' b')
    (zigzag_natsq (pf a) (pf a') (pg b))^
    (zigzag_natsq (pf a) (pf a') (pg b'))^
    (ap (fun q => K (joinl a) @ q) (zG a a' b))
    (ap (fun q => K (joinl a) @ q) (zG a a' b'))
    (betaN b) (betaN b') h).
Defined.

Example filler_witness_unchanged {A B C D : Type}
  {f f' : A -> C} {g g' : B -> D} (pf : f == f') (pg : g == g')
  {a a' : A} {b b' : B} (h : zigzag a a' b = zigzag a a' b')
  : join_zigzag_filler_homotopic pf pg h = legacy_filler_homotopic pf pg h
  := idpath.
