From HoTT Require Import Basics.
Require Import Types.Paths.
Require Import Homotopy.Join.Core.

Local Open Scope path_scope.

(** * Homotopies out of products of joins *)

(** Four vertex homotopies and four edge squares extend to a homotopy when supplied with their mixed cube. The presentation is symmetric in the two join coordinates; the implementation chooses the first coordinate as the outer induction. *)
Section Homotopy2.
  Context {A B C D P : Type}
    (f g : Join A B -> Join C D -> P)
    (h00 : forall a c, f (joinl a) (joinl c) = g (joinl a) (joinl c))
    (h01 : forall a d, f (joinl a) (joinr d) = g (joinl a) (joinr d))
    (h10 : forall b c, f (joinr b) (joinl c) = g (joinr b) (joinl c))
    (h11 : forall b d, f (joinr b) (joinr d) = g (joinr b) (joinr d))
    (hh0 : forall a c d, ap (f (joinl a)) (jglue c d) @ h01 a d
      = h00 a c @ ap (g (joinl a)) (jglue c d))
    (hh1 : forall b c d, ap (f (joinr b)) (jglue c d) @ h11 b d
      = h10 b c @ ap (g (joinr b)) (jglue c d)).

  Let u a b y := ap (fun x => f x y) (jglue a b).
  Let v a b y := ap (fun x => g x y) (jglue a b).

  Context
    (hv0 : forall a b c, u a b (joinl c) @ h10 b c
      = h00 a c @ v a b (joinl c))
    (hv1 : forall a b d, u a b (joinr d) @ h11 b d
      = h01 a d @ v a b (joinr d))
    (hc : forall a b c d,
      concat_natural (ap (f (joinl a)) (jglue c d))
        (ap (f (joinr b)) (jglue c d))
        (ap (g (joinr b)) (jglue c d))
        (u a b (joinl c)) (u a b (joinr d))
        (h10 b c) (h11 b d) (concat_Ap (u a b) (jglue c d))
        (hh1 b c d) @ (hv0 a b c @@ 1)
      = (1 @@ hv1 a b d) @ concat_natural
        (ap (f (joinl a)) (jglue c d))
        (ap (g (joinl a)) (jglue c d))
        (ap (g (joinr b)) (jglue c d))
        (h00 a c) (h01 a d)
        (v a b (joinl c)) (v a b (joinr d))
        (hh0 a c d) (concat_Ap (v a b) (jglue c d))).

  Let hl a := Join_ind_FlFr (f (joinl a)) (g (joinl a))
    (h00 a) (h01 a) (hh0 a).
  Let hr b := Join_ind_FlFr (f (joinr b)) (g (joinr b))
    (h10 b) (h11 b) (hh1 b).

  Definition Join_ind2_FlFr_glue (a : A) (b : B)
    : forall y, u a b y @ hr b y = hl a y @ v a b y.
  Proof.
    snapply Join_ind.
    - exact (hv0 a b).
    - exact (hv1 a b).
    - intros c d.
      napply (transport_naturality_square (u a b) (v a b)
        (hl a) (hr b) (jglue c d)).
      lhs napply (ap (concat_natural
        (ap (f (joinl a)) (jglue c d))
        (ap (f (joinr b)) (jglue c d))
        (ap (g (joinr b)) (jglue c d))
        (u a b (joinl c)) (u a b (joinr d))
        (h10 b c) (h11 b d) (concat_Ap (u a b) (jglue c d)))
        (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d) @@ 1).
      rhs napply (1 @@ ap (fun q => concat_natural
        (ap (f (joinl a)) (jglue c d))
        (ap (g (joinl a)) (jglue c d))
        (ap (g (joinr b)) (jglue c d))
        (h00 a c) (h01 a d)
        (v a b (joinl c)) (v a b (joinr d)) q
        (concat_Ap (v a b) (jglue c d)))
        (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d)).
      exact (hc a b c d).
  Defined.

  Definition Join_ind2_FlFr : forall x y, f x y = g x y.
  Proof.
    intros x y; revert x.
    snapply Join_ind_FlFr.
    - exact (fun a => hl a y).
    - exact (fun b => hr b y).
    - exact (fun a b => Join_ind2_FlFr_glue a b y).
  Defined.
End Homotopy2.

(** ** The mixed computation of nested homotopy induction *)

(** The outer homotopy eliminator's glue comparison is itself constructed by dependent join induction. Its variation in the second coordinate retains both outer beta paths and the exact chosen inner mixed comparison. *)
Section NestedComputation.
  Universes u v w z s t p.
  Context {A : Type@{u}} {B : Type@{v}}
    {C : Type@{w}} {D : Type@{z}} {T : Type@{p}}
    (f g : Join@{u v s} A B -> Join@{w z t} C D -> T)
    (hl : forall a y, f (joinl a) y = g (joinl a) y)
    (hr : forall b y, f (joinr b) y = g (joinr b) y).
  Let Q a b y := ap (fun x => f x y) (jglue a b) @ hr b y
    = hl a y @ ap (fun x => g x y) (jglue a b).
  Context (gl : forall a b c, Q a b (joinl c))
    (gr : forall a b d, Q a b (joinr d))
    (gm : forall a b c d,
      transport (Q a b) (jglue c d) (gl a b c) = gr a b d).
  Let edge a b := Join_ind (Q a b) (gl a b) (gr a b) (gm a b).
  Let h x y := Join_ind_FlFr (fun x => f x y) (fun x => g x y)
    (fun a => hl a y) (fun b => hr b y) (fun a b => edge a b y) x.
  Let beta a b y : concat_Ap (fun x => h x y) (jglue a b) = edge a b y
    := Join_ind_FlFr_beta_jglue _ _ _ _ _ a b.

  Definition Join_ind_FlFr_ind_beta_jglue_jglue
    (a : A) (b : B) (c : C) (d : D)
    : apD (fun y => concat_Ap (fun x => h x y) (jglue a b))
        (jglue c d)
      = (ap (transport (Q a b) (jglue c d)) (beta a b (joinl c))
          @ gm a b c d) @ (beta a b (joinr d))^.
  Proof.
    lhs napply (apD_homotopic (beta a b) (jglue c d)).
    exact ((1 @@ Join_ind_beta_jglue _ _ _ _ c d) @@ 1).
  Defined.
End NestedComputation.

(** * Dependent extension from two compatible left faces *)

(** The two faces have one arbitrary join coordinate each. Their intersection comparison is supplied, not inferred from matching types. Right-constructor data are chosen by transport from [a0] and [c0], leaving precisely the mixed glue comparison as an input. *)
Section FromLeftFaces.
  Universes u v w z s t p.
  Context {A : Type@{u}} {B : Type@{v}}
    {C : Type@{w}} {D : Type@{z}}
    (P : Join@{u v s} A B -> Join@{w z t} C D -> Type@{p})
    (a0 : A) (c0 : C)
    (left : forall a y, P (joinl a) y)
    (bottom : forall x c, P x (joinl c))
    (agree : forall a c, bottom (joinl a) c = left a (joinl c)).

  Definition Join_ind2_from_left_right (b : B) (y : Join C D)
    : P (joinr b) y
    := transport (fun x => P x y) (jglue a0 b) (left a0 y).

  Definition JoinInd2LeftGlue (a : A) (b : B) (y : Join C D)
    := transport (fun x => P x y) (jglue a b) (left a y)
      = Join_ind2_from_left_right b y.

  (** The comparison on the transported right row retains the chosen intersection path and the dependent application of [bottom]. *)
  Definition Join_ind2_from_left_overlap_r (b : B) (c : C)
    : bottom (joinr b) c = Join_ind2_from_left_right b (joinl c)
    := (apD (fun x => bottom x c) (jglue a0 b))^
      @ ap (transport (fun x => P x (joinl c)) (jglue a0 b))
        (agree a0 c).

  Definition Join_ind2_from_left_glue_l (a : A) (b : B) (c : C)
    : JoinInd2LeftGlue a b (joinl c)
    := ((apD (fun x => bottom x c) (jglue a b))^
        @ ap (transport (fun x => P x (joinl c)) (jglue a b))
          (agree a c))^
      @ Join_ind2_from_left_overlap_r b c.

  Definition Join_ind2_from_left_glue_r (a : A) (b : B) (d : D)
    : JoinInd2LeftGlue a b (joinr d)
    := transport (JoinInd2LeftGlue a b) (jglue c0 d)
      (Join_ind2_from_left_glue_l a b c0).

  (** At [a0] the mixed comparison is supplied by the canonical contraction of an inverse followed by its path. This is a computation with the specified side, not uniqueness of fillers. *)
  Definition Join_ind2_from_left_mixed_base (b : B) (c : C) (d : D)
    : transport (JoinInd2LeftGlue a0 b) (jglue c d)
        (Join_ind2_from_left_glue_l a0 b c)
      = Join_ind2_from_left_glue_r a0 b d.
  Proof.
    refine (ap (transport (JoinInd2LeftGlue a0 b) (jglue c d))
      (concat_Vp _) @ _).
    refine (apD (fun y => idpath (Join_ind2_from_left_right b y))
      (jglue c d) @ _).
    refine ((apD (fun y => idpath (Join_ind2_from_left_right b y))
      (jglue c0 d))^ @ _).
    exact (ap (transport (JoinInd2LeftGlue a0 b) (jglue c0 d))
      (concat_Vp _)^).
  Defined.

  Context (mixed : forall a b c d,
    transport (JoinInd2LeftGlue a b) (jglue c d)
      (Join_ind2_from_left_glue_l a b c)
    = Join_ind2_from_left_glue_r a b d).

  Definition Join_ind2_from_left_glue (a : A) (b : B)
    : forall y, JoinInd2LeftGlue a b y
    := Join_ind _ (Join_ind2_from_left_glue_l a b)
      (Join_ind2_from_left_glue_r a b) (mixed a b).

  Definition Join_ind2_from_left (x : Join A B) (y : Join C D) : P x y
    := Join_ind (fun x => P x y) (fun a => left a y)
      (fun b => Join_ind2_from_left_right b y)
      (fun a b => Join_ind2_from_left_glue a b y) x.

  (** The other whole face is retained up to the specified intersection comparison. At left constructors this computes to [agree]. *)
  Definition Join_ind2_from_left_overlap (x : Join A B) (c : C)
    : bottom x c = Join_ind2_from_left x (joinl c).
  Proof.
    revert x; snapply Join_ind.
    - exact (fun a => agree a c).
    - exact (fun b => Join_ind2_from_left_overlap_r b c).
    - intros a b.
      lhs napply (transport_paths_FlFr_D
        (f:=fun x => bottom x c)
        (g:=fun x => Join_ind2_from_left x (joinl c))
        (jglue a b) (agree a c)).
      lhs napply (1 @@ Join_ind_beta_jglue _ _ _ _ a b).
      exact (concat_p_Vp _ _).
  Defined.
End FromLeftFaces.
