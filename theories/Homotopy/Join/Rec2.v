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
