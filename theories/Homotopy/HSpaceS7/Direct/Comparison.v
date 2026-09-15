From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Spaces.Spheres Homotopy.Suspension Homotopy.Join.Core.
Require Import Homotopy.HSpaceS7.Direct.Core.
Require Import Homotopy.HSpaceS7.Direct.Normalization.

Local Set Universe Minimization ToSet.
Local Open Scope path_scope.

(** * The remaining eta comparison and the original mixed boundary *)
Module S7DirectComparison.
Include S7DirectNormalization.
Section Comparison.
  Universe u.
  Context `{Univalence}.
  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation Mixed := (S7DirectCore.Mixed@{u}).
  Local Notation eta_face := (S7DirectNormalization.eta_face@{u}).
  Local Notation eta_face_middle :=
    (S7DirectNormalization.eta_face_middle@{u}).
  Local Notation eta_edge := (S7DirectNormalization.eta_edge@{u}).
  Local Notation computed_pasting :=
    (S7DirectNormalization.computed_pasting@{u}).
  Local Notation equiv_mixed_expansion :=
    (S7DirectNormalization.equiv_mixed_expansion@{u}).
  Local Notation eta_computed_edge :=
    (S7DirectNormalization.eta_computed_edge@{u}).
  Local Notation computed_pasting_eta_factor :=
    (S7DirectNormalization.computed_pasting_eta_factor@{u}).
  Local Notation eta_computed_edge_ratio :=
    (S7DirectNormalization.eta_computed_edge_ratio@{u}).

  (** A comparison of the whole sections suffices only when its left restriction is the specified middle comparison. Dependent naturality then identifies its right value with every edge ratio, including the unit-labelled one. This does not construct the required section. *)
  Definition eta_edge_comparison_of_section (a b c d : C)
    (K : forall y : J, eta_face a b c d y = eta_face a b North d y)
    (K_left : forall s : C, K (joinl s)
      = eta_face_middle a b s c d @ (eta_face_middle a b s North d)^)
    (s t : C)
    : eta_edge a b s t c d
        @ ((eta_edge a b North t c d)^ @ eta_edge a b North t North d)
      = eta_edge a b s t North d.
  Proof.
    pose (edge := fun s : C => apD_homotopic_adjusted K (jglue s t)
      (eta_face_middle a b s c d) (eta_face_middle a b s North d)
      (K_left s)).
    lhs_V napply (1 @@ moveL_Vp _ _ _ (edge North)).
    exact (edge s).
  Defined.

  (** Cancel the common whole-face transport factors in the existing expanded equation. Endpoint independence alone is automatic via the [s = North] edge ratio; the remaining 4-path says that every [s] gives that same comparison. *)
  Definition equiv_mixed_eta (a b s t c d : C)
    : ((eta_edge a b s t c d)^ @ eta_edge a b s t North d
        = (eta_edge a b North t c d)^ @ eta_edge a b North t North d)
      <~> Mixed a b s t c d.
  Proof.
    refine (equiv_mixed_expansion a b s t c d oE _).
    refine (equiv_pasting_factors
      (computed_pasting a b s t c d) (computed_pasting a b s t North d)
      (computed_pasting a b North t c d)
      (computed_pasting a b North t North d)
      (eta_computed_edge a b s t c d)
      (eta_computed_edge a b s t North d)
      (eta_computed_edge a b North t c d)
      (eta_computed_edge a b North t North d)
      (computed_pasting_eta_factor a b s t c d)
      (computed_pasting_eta_factor a b s t North d)
      (computed_pasting_eta_factor a b North t c d)
      (computed_pasting_eta_factor a b North t North d) oE _).
    exact (equiv_concat_lr (eta_computed_edge_ratio a b s t c d)
      (eta_computed_edge_ratio a b North t c d)^).
  Defined.
End Comparison.
End S7DirectComparison.
