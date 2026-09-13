From HoTT Require Import Basics Types.Paths.
From HoTT Require Import Homotopy.Join.Core Homotopy.Join.Rec2.

Local Open Scope path_scope.

(** Test the computation of the general comparison, with arbitrary vertex paths, side squares, and a supplied mixed cube. No truncation or extensionality is used. *)
Section Computation.
  Universe a b c d p.
  Context {A : Type@{a}} {B : Type@{b}} {C : Type@{c}}
    {D : Type@{d}} {P : Type@{p}}
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

  Let H := Join_ind2_FlFr f g h00 h01 h10 h11 hh0 hh1 hv0 hv1 hc.
  Let glue := Join_ind2_FlFr_glue
    f g h00 h01 h10 h11 hh0 hh1 hv0 hv1 hc.

  Example corner_ll (a : A) (c : C) : H (joinl a) (joinl c) = h00 a c
    := idpath.
  Example corner_lr (a : A) (d : D) : H (joinl a) (joinr d) = h01 a d
    := idpath.
  Example corner_rl (b : B) (c : C) : H (joinr b) (joinl c) = h10 b c
    := idpath.
  Example corner_rr (b : B) (d : D) : H (joinr b) (joinr d) = h11 b d
    := idpath.

  Example row_l (a : A) (c : C) (d : D)
    : concat_Ap (H (joinl a)) (jglue c d) = hh0 a c d.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
  Defined.
  Example row_r (b : B) (c : C) (d : D)
    : concat_Ap (H (joinr b)) (jglue c d) = hh1 b c d.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
  Defined.
  Example column (a : A) (b : B) (y : Join C D)
    : concat_Ap (fun x => H x y) (jglue a b) = glue a b y.
  Proof.
    exact (Join_ind_FlFr_beta_jglue _ _ _ _ _ a b).
  Defined.
  Example column_l (a : A) (b : B) (c : C)
    : glue a b (joinl c) = hv0 a b c := idpath.
  Example column_r (a : A) (b : B) (d : D)
    : glue a b (joinr d) = hv1 a b d := idpath.
End Computation.
