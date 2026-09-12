From HoTT Require Import Basics Types.Paths Types.Universe.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1.
From HoTT Require Import Homotopy.HSpaceS3 Homotopy.HSpaceS7.
From HoTT Require Import Homotopy.Join.Core Homotopy.CayleyDickson.
From HoTT Require Import Homotopy.Suspension.

Local Set Universe Minimization ToSet.

Local Open Scope path_scope.

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
  (** Full equivariance and the last-left associator require no extra circle or doubled-associativity hypothesis. *)
  Check (fun r : Sphere 1 =>
    cd_op_diagonal_equivariance_glue_glue@{Set} (X:=psphere 1) r a b c d).
  Check (fun (r : Sphere 1) (x y : Join (Sphere 1) (Sphere 1)) =>
    cd_op_diagonal_equivariance@{Set} (X:=psphere 1) r x y).
  Check (fun (x y : Join (Sphere 1) (Sphere 1)) (r : Sphere 1) =>
    cd_assoc_last_joinl@{Set} (X:=psphere 1) x y r).
  (** The unit-glue symmetry also gives a right-copy associator and its compatibility with the left one at the two unit labels. *)
  Check (fun (x y : Join (Sphere 1) (Sphere 1)) =>
    cd_op_chi_equivariance@{Set} (X:=psphere 1) x y).
  Check (fun (x y : Join (Sphere 1) (Sphere 1)) (r : Sphere 1) =>
    cd_assoc_last_joinr@{Set} (X:=psphere 1) x y r).
  Check (fun (x y : Join (Sphere 1) (Sphere 1)) =>
    cd_assoc_last_glue_unit@{Set} (X:=psphere 1) x y).
End CircleNormalForm.

(** The four preceding-argument constructor pairs have actual scalar-loop nullhomotopies. These do not assert the join-glue cases needed for arbitrary preceding arguments. *)
Section ScalarLoopComputations.
  Context `{Univalence} (a b : Sphere 1).

  Definition circle_scalar_loop_ll (d : Sphere 1)
    : ap (cd_assoc_last_transport (X:=psphere 1) (joinl a) (joinl b) d)
        (merid North @ (merid South)^) = 1
    := cd_assoc_last_transport_loop_ll@{Set} a b d
        (merid North @ (merid South)^).
  Definition circle_scalar_loop_lr (d : Sphere 1)
    : ap (cd_assoc_last_transport (X:=psphere 1) (joinl a) (joinr b) d)
        (merid North @ (merid South)^) = 1
    := cd_assoc_last_transport_loop_lr@{Set} a b d
        (merid North @ (merid South)^).
  Definition circle_scalar_loop_rl (d : Sphere 1)
    : ap (cd_assoc_last_transport (X:=psphere 1) (joinr a) (joinl b) d)
        (merid North @ (merid South)^) = 1
    := cd_assoc_last_transport_loop_rl@{Set} a b d
        (merid North @ (merid South)^).
  Definition circle_scalar_loop_rr (d : Sphere 1)
    : ap (cd_assoc_last_transport (X:=psphere 1) (joinr a) (joinr b) d)
        (merid North @ (merid South)^) = 1
    := cd_assoc_last_transport_loop_rr@{Set} a b d
        (merid North @ (merid South)^).

  (** The second-circle comparisons retain the particular proofs above. *)
  Example circle_scalar_loop_ll_coherence
    : transport (fun d => ap (cd_assoc_last_transport (X:=psphere 1)
        (joinl a) (joinl b) d) (merid North @ (merid South)^) = 1)
        (merid North @ (merid South)^) (circle_scalar_loop_ll North)
      = circle_scalar_loop_ll North
    := apD circle_scalar_loop_ll (merid North @ (merid South)^).
  Example circle_scalar_loop_lr_coherence
    : transport (fun d => ap (cd_assoc_last_transport (X:=psphere 1)
        (joinl a) (joinr b) d) (merid North @ (merid South)^) = 1)
        (merid North @ (merid South)^) (circle_scalar_loop_lr North)
      = circle_scalar_loop_lr North
    := apD circle_scalar_loop_lr (merid North @ (merid South)^).
  Example circle_scalar_loop_rl_coherence
    : transport (fun d => ap (cd_assoc_last_transport (X:=psphere 1)
        (joinr a) (joinl b) d) (merid North @ (merid South)^) = 1)
        (merid North @ (merid South)^) (circle_scalar_loop_rl North)
      = circle_scalar_loop_rl North
    := apD circle_scalar_loop_rl (merid North @ (merid South)^).
  Example circle_scalar_loop_rr_coherence
    : transport (fun d => ap (cd_assoc_last_transport (X:=psphere 1)
        (joinr a) (joinr b) d) (merid North @ (merid South)^) = 1)
        (merid North @ (merid South)^) (circle_scalar_loop_rr North)
      = circle_scalar_loop_rr North
    := apD circle_scalar_loop_rr (merid North @ (merid South)^).
End ScalarLoopComputations.

(** Check the proposed two-circle elimination and its chosen constructor/glue computations. The two loop inputs below are hypotheses of this regression only: no library proof of them for arbitrary [x,y] has been supplied. *)
Section ScalarLoopAssembly.
  Context `{Univalence} (x y : Join (Sphere 1) (Sphere 1)).

  Definition scalar_loop_target (d : Sphere 1)
    := ap (cd_assoc_last_transport (X:=psphere 1) x y d)
         (merid North @ (merid South)^) = 1.

  Context (m0 : scalar_loop_target North)
    (m1 : transport scalar_loop_target (merid North @ (merid South)^) m0 = m0).

  Definition scalar_loop_family : forall d, scalar_loop_target d
    := Sph1_ind scalar_loop_target m0 m1.

  Definition scalar_loop_glue (c d : Sphere 1)
    : cd_assoc_last_transport (X:=psphere 1) x y d c
      = cd_assoc_last_joinr_transport (X:=psphere 1) x y d.
  Proof.
    revert c; snapply Sph1_ind.
    - reflexivity.
    - nrefine (equiv_naturality_transport
        (cd_assoc_last_transport (X:=psphere 1) x y d)
        (fun _ => cd_assoc_last_joinr_transport (X:=psphere 1) x y d)
        (merid North @ (merid South)^) 1 1 _).
      exact ((scalar_loop_family d @@ 1)
        @ (1 @@ ap_const (merid North @ (merid South)^) _)^).
  Defined.

  Definition associator_from_scalar_loops
    : forall z, cd_op (cd_op x y) z = cd_op x (cd_op y z).
  Proof.
    snapply Join_ind.
    - exact (cd_assoc_last_joinl x y).
    - exact (cd_assoc_last_joinr_transport x y).
    - exact scalar_loop_glue.
  Defined.

  Example scalar_loop_family_at_unit : scalar_loop_family North = m0
    := idpath.
  Example scalar_loop_glue_at_unit (d : Sphere 1)
    : scalar_loop_glue North d = 1 := idpath.
  Example scalar_loop_associator_left (c : Sphere 1)
    : associator_from_scalar_loops (joinl c) = cd_assoc_last_joinl x y c
    := idpath.
  Example scalar_loop_associator_right (d : Sphere 1)
    : associator_from_scalar_loops (joinr d)
      = cd_assoc_last_joinr_transport x y d := idpath.
  Example scalar_loop_associator_glue (c d : Sphere 1)
    : apD associator_from_scalar_loops (jglue c d) = scalar_loop_glue c d.
  Proof.
    exact (Join_ind_beta_jglue _ _ _ _ c d).
  Defined.
End ScalarLoopAssembly.

(** The full rectangle family is still a required input. *)
Example sphere_seven_hspace_conditional `{Univalence}
  (h : forall (a b : Sphere 1) (u v : Join (Sphere 1) (Sphere 1)),
    cd_associativity_rectangle (X:=psphere 1) a b u v)
  : IsHSpace@{Set} (psphere 7) := hspace_s7_from_rectangle h.
