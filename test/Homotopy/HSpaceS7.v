From HoTT Require Import Basics Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
From HoTT Require Import Homotopy.HSpaceS3 Homotopy.HSpaceS7.
From HoTT Require Import Homotopy.Join.Core Homotopy.CayleyDickson.

(** All four scalar corners are available from circle commutativity, without assuming associativity of its double. *)
Example circle_rectangle_corners `{Univalence} (a b c d : Sphere 1)
  : (cd_associativity_rectangle (X:=psphere 1) a b (joinl c) (joinl d)
    * cd_associativity_rectangle (X:=psphere 1) a b (joinl c) (joinr d)
    * cd_associativity_rectangle (X:=psphere 1) a b (joinr c) (joinl d)
    * cd_associativity_rectangle (X:=psphere 1) a b (joinr c) (joinr d))%type
  := (cd_associativity_rectangle_ll@{Set} a b c d,
      cd_associativity_rectangle_lr@{Set} a b c d,
      cd_associativity_rectangle_rl@{Set} a b c d,
      cd_associativity_rectangle_rr@{Set} a b c d).

(** The middle-normalized choices have both glue coherences in the last argument, without any further coherence assumption. *)
Example circle_rectangle_middle_l_glue `{Univalence}
  (a b c d e : Sphere 1)
  : transport (cd_associativity_rectangle (X:=psphere 1) a b (joinl c))
      (jglue d e)
      (cd_associativity_rectangle_middle_l a b c (joinl d))
    = cd_associativity_rectangle_middle_l a b c (joinr e)
  := apD (cd_associativity_rectangle_middle_l a b c) (jglue d e).

Example circle_rectangle_middle_r_glue `{Univalence}
  (a b c d e : Sphere 1)
  : transport (cd_associativity_rectangle (X:=psphere 1) a b (joinr c))
      (jglue d e)
      (cd_associativity_rectangle_middle_r a b c (joinl d))
    = cd_associativity_rectangle_middle_r a b c (joinr e)
  := apD (cd_associativity_rectangle_middle_r a b c) (jglue d e).

(** The mixed-filler normal form specializes to the chosen circle data at [Set], without any equivariance or doubled-associativity hypothesis. *)
Section CircleNormalForm.
  Context `{Univalence} (a b c d : Sphere 1).
  Check (cd_op_diamond_normalize@{Set} (X:=psphere 1) a b c d).
  (** The parameter-independent mixed comparison needs no further circle coherence input. *)
  Check (fun r : Sphere 1 =>
    cd_op_diamond_diagonal@{Set} (X:=psphere 1) a b c d r).
  Check (fun (r : Sphere 1) (y : Join (Sphere 1) (Sphere 1)) =>
    cd_op_diagonal_equivariance_joinl@{Set} (X:=psphere 1) r a y).
  Check (fun (r : Sphere 1) (y : Join (Sphere 1) (Sphere 1)) =>
    cd_op_diagonal_equivariance_joinr@{Set} (X:=psphere 1) r b y).
  Check (fun r : Sphere 1 =>
    cd_op_diagonal_equivariance_glue_joinl@{Set} (X:=psphere 1) r a b c).
  Check (fun r : Sphere 1 =>
    cd_op_diagonal_equivariance_glue_joinr@{Set} (X:=psphere 1) r a b d).
End CircleNormalForm.

(** The full rectangle family is still a required input. *)
Example sphere_seven_hspace_conditional `{Univalence}
  (h : forall (a b : Sphere 1) (u v : Join (Sphere 1) (Sphere 1)),
    cd_associativity_rectangle (X:=psphere 1) a b u v)
  : IsHSpace@{Set} (psphere 7) := hspace_s7_from_rectangle h.
