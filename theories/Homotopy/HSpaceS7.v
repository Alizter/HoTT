From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pEquiv.
Require Import Spaces.Spheres.
Require Import Homotopy.HSpace.Core Homotopy.HSpaceS1 Homotopy.HSpaceS3.
Require Import Homotopy.CayleyDickson Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.JoinSusp.
Require Export Homotopy.HSpaceS7.LeftScalar Homotopy.HSpaceS7.Balanced.

Local Set Universe Minimization ToSet.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * The remaining input for the 7-sphere H-space *)

(** The executable outline is [S7ProofOutline] below. Its four named section hypotheses are precisely the missing proofs: three sides and the dependent mixed case of double join induction on the scalar-loop proofs. Every subsequent assembly step, through the final H-space transfer, is implemented here. No unconditional [hspace_s7] has been constructed. The detailed development plan is in [doc/HSPACE_S7.md]; [test/Homotopy/HSpaceS7Outline.v] checks the actual implementation's computation rules.
<<
  four constructor loop proofs
    -> one proved join-glue comparison, three open sides, and one open mixed coherence
    -> loop vanishing for arbitrary x,y,d
    -> circle induction in c: the last join glue
    -> join induction in z: the associator
    -> reverse paths: Associative cd_op
    -> second doubling and sphere transfer: IsHSpace (psphere 7).
>>
The rectangle-based constructions below are alternative conditional interfaces, not additional inputs to this route. *)

(** Work in join coordinates for the second doubling. Only the final H-space structure is transferred to a suspension sphere. *)
Definition pequiv_iterated_join_s1_s7
  : pjoin (pjoin (psphere 1) (Sphere 1)) (Join (Sphere 1) (Sphere 1))
      <~>* psphere 7.
Proof.
  refine (pequiv_pjoin_sphere 3 3 o*E _).
  snapply Build_pEquiv'.
  - exact (equiv_functor_join (pequiv_pjoin_sphere 1 1)
      (pequiv_pjoin_sphere 1 1)).
  - reflexivity.
Defined.

(** The diagonal circle-action approach starts with [cd_diamond_parameter_translate] and [cd_op_diamond_normalize]. The comparison [cd_op_diamond_diagonal] uses connectedness and 1-truncation of the scalars to make each vertex path independent of the other labels. The dependent mixed case [cd_op_diagonal_equivariance_glue_glue] converts that comparison using the actual recursor computations and the four specified side faces. Thus [cd_op_diagonal_equivariance] is a full homotopy and gives [cd_assoc_last_joinl]. The unit join glue additionally gives [cd_chi_homotopic_id], whose specified symmetry homotopy [cd_op_chi_equivariance] yields [cd_assoc_last_joinr]. This construction does not assert an equality between scalar-normalized reflected diamonds. Both partial associators have arbitrary preceding join arguments, and [cd_assoc_last_glue_unit] proves their compatibility across the unit join glue. *)

(** For assembling an associator, [cd_assoc_last_joinr_transport] is a different right partial associator: it transports the unchanged left associator at the unit along [jglue mon_unit d]. Thus the whole unit-left-label boundary is automatic. At [d = mon_unit], [cd_assoc_last_glue_unit] compares this choice with the symmetry-based right associator; no comparison at arbitrary [d] is required or asserted.

Writing [T d c := cd_assoc_last_transport x y d c], the remaining glue condition is [T d c = T d mon_unit]. With [ell := merid North @ (merid South)^], two applications of [Sph1_ind] reduce this to the following specified computations, uniformly in arbitrary join elements [x,y]:
<<
  M d := (ap (T d) ell = 1)
  m0 : M North
  m1 : transport M ell m0 = m0.
>>
The four lemmas [cd_assoc_last_transport_loop_ll], [cd_assoc_last_transport_loop_lr], [cd_assoc_last_transport_loop_rl], and [cd_assoc_last_transport_loop_rr] prove loop vanishing when the preceding arguments are constructors. They are families in [d], so their particular second-label coherences follow by [apD]. [S7LeftScalar.loop_y_joinl] extends the left row across its join glue. The other three sides and their mixed compatibility remain open. Consequently neither [m0] nor [m1] is supplied for arbitrary [x,y], and no unconditional doubled associativity is asserted here. Connectedness and scalar truncation do not fill these join-valued coherence goals. *)

(** ** Executable outline with four open comparisons *)

(** Short names are confined to this module. All definitions after the gap hypotheses remain conditional on the hypotheses they use; none is registered as an unconditional associativity or H-space instance. *)
Module S7ProofOutline.
Section Construction.
  Context `{Univalence}.

  (** Share the scalar witnesses with the proved left row; independent universe instances of truncation proofs need not be definitionally interchangeable. *)
  Local Existing Instances S7LeftScalar.circle_imaginaroid
    S7LeftScalar.circle_spheroid S7LeftScalar.circle_associative
    S7LeftScalar.circle_commutative S7LeftScalar.circle_connected
    S7LeftScalar.circle_truncated.

  Local Notation C := (Sphere 1).
  Local Notation J := (Join@{Set Set Set} C C).
  Local Notation mu := (cd_op@{Set} (X:=psphere 1)).
  Local Notation AL := (cd_assoc_last_joinl@{Set} (X:=psphere 1)).
  Local Notation AR := (cd_assoc_last_joinr_transport@{Set} (X:=psphere 1)).
  Local Notation T := (cd_assoc_last_transport@{Set} (X:=psphere 1)).
  Local Notation ell :=
    ((merid (North : Sphere 0) @ (merid South)^) : (North = North :> C)).

  (** Goal: make [T x y d] constant in its last scalar argument. Keep this local family fixed so the same inferred circle data is shared throughout the construction. *)
  Let M (x y : J) (d : C) := ap (T x y d) ell = 1.

  (** Step 1 (proved): the four constructor-pair loop computations. *)
  Definition m_ll (a b d : C) : M (joinl a) (joinl b) d
    := cd_assoc_last_transport_loop_ll@{Set} a b d ell.
  Definition m_lr (a b d : C) : M (joinl a) (joinr b) d
    := cd_assoc_last_transport_loop_lr@{Set} a b d ell.
  Definition m_rl (a b d : C) : M (joinr a) (joinl b) d
    := cd_assoc_last_transport_loop_rl@{Set} a b d ell.
  Definition m_rr (a b d : C) : M (joinr a) (joinr b) d
    := cd_assoc_last_transport_loop_rr@{Set} a b d ell.

  Local Opaque m_ll m_lr m_rl m_rr.

  (** Former OPEN 1 is proved by the first-left-scalar associator and its overlap with [AL]. Its corner values retain the original [m_ll] and [m_lr] witnesses. *)
  Local Notation loop_y_joinl :=
    (fun a b b' d => S7LeftScalar.loop_y_joinl
      cd_diamond_susp a b b' d ell).

  (** OPEN 2: the analogous y-glue with x in the right copy. Use the right equivariance row and retain its inverse-edge computations [ap_V] and [inverse_natural]; it is not obtained by declaring a reflection symmetry of the diamond. *)
  Context (loop_y_joinr : forall a b b' d : C,
    transport (fun y => M (joinr a) y d) (jglue b b') (m_rl a b d)
      = m_rr a b' d).

  (** OPEN 3: compare [ll] with [rl] along an x-glue. [cd_assoc_middle_joinl] now supplies partial associativity with this middle scalar and both outer arguments arbitrary. Comparing its choices with [AL] and the original corner witnesses is still required before it gives this loop comparison. The relevant existing equivariance face is [cd_op_diagonal_equivariance_glue_joinl]. *)
  Context (loop_x_joinl : forall a a' b d : C,
    transport (fun x => M x (joinl b) d) (jglue a a') (m_ll a b d)
      = m_rl a' b d).

  (** OPEN 4: compare [lr] with [rr] along an x-glue. Use [cd_op_diagonal_equivariance_glue_joinr] and the centers supplied by [cd_assoc_rr b d]. Preserve the reversed-edge beta paths rather than treating this as a formal renaming of OPEN 3. *)
  Context (loop_x_joinr : forall a a' b d : C,
    transport (fun x => M x (joinr b) d) (jglue a a') (m_lr a b d)
      = m_rr a' b d).

  (** Step 2: the proved left comparison and OPEN 2 assemble the rows. *)
  Definition loop_row_l (a d : C) : forall y : J, M (joinl a) y d.
  Proof.
    snapply Join_ind.
    - exact (fun b => m_ll a b d).
    - exact (fun b => m_lr a b d).
    - exact (fun b b' => loop_y_joinl a b b' d).
  Defined.

  Definition loop_row_r (a d : C) : forall y : J, M (joinr a) y d.
  Proof.
    snapply Join_ind.
    - exact (fun b => m_rl a b d).
    - exact (fun b => m_rr a b d).
    - exact (fun b b' => loop_y_joinr a b b' d).
  Defined.

  (** This is the remaining x-glue family. It contains both previously chosen y-glue comparisons through the rows. *)
  Definition XGlue (a a' d : C) (y : J)
    := transport (fun x => M x y d) (jglue a a') (loop_row_l a d y)
         = loop_row_r a' d y.

  (** OPEN 5: compatibility of all four chosen sides. First expose [XGlue] and use [Join_ind_beta_jglue] for both rows. Normalize the two-variable transports before comparing the resulting pastings of OPEN 1--4. Any remaining comparison of actual mixed fillers must then be proved, not inferred from matching boundaries. If necessary, specialize that residual statement to [cd_diamond_susp] and its north, south, and meridian computations. *)
  Context (loop_mixed : forall a a' b b' d : C,
    transport (XGlue a a' d) (jglue b b') (loop_x_joinl a a' b d)
      = loop_x_joinr a a' b' d).

  (** Step 3: finish double join induction in x,y. No further missing inputs occur below this point. *)
  Definition loop_column (a a' d : C) : forall y : J, XGlue a a' d y.
  Proof.
    snapply Join_ind.
    - exact (fun b => loop_x_joinl a a' b d).
    - exact (fun b => loop_x_joinr a a' b d).
    - exact (fun b b' => loop_mixed a a' b b' d).
  Defined.

  Definition all_scalar_loops (x y : J) (d : C) : M x y d.
  Proof.
    revert x; snapply Join_ind.
    - exact (fun a => loop_row_l a d y).
    - exact (fun a => loop_row_r a d y).
    - exact (fun a a' => loop_column a a' d y).
  Defined.

  (** These are (I) and (II) of the two-circle formulation. Since all five comparisons are families in [d], both follow from the assembled family and are not additional hypotheses. *)
  Let m0 (x y : J) : M x y North := all_scalar_loops x y North.
  Let m1 (x y : J) : transport (M x y) ell (m0 x y) = m0 x y
    := apD (all_scalar_loops x y) ell.

  (** Step 4: circle induction in c gives the last join glue. Its unit case is reflexivity because [AR] was chosen by transport. *)
  Definition last_glue (x y : J) (c d : C)
    : transport (fun z => mu (mu x y) z = mu x (mu y z))
        (jglue c d) (AL x y c) = AR x y d.
  Proof.
    change (T x y d c = T x y d North).
    revert c; snapply Sph1_ind.
    - reflexivity.
    - nrefine (equiv_naturality_transport (T x y d)
        (fun _ => T x y d North) ell 1 1 _).
      exact ((all_scalar_loops x y d @@ 1) @ (1 @@ ap_const ell _)^).
  Defined.

  (** Step 5: join induction in z, retaining the existing left associator and the transported right choice. *)
  Definition associator (x y : J)
    : forall z : J, mu (mu x y) z = mu x (mu y z).
  Proof.
    snapply Join_ind.
    - exact (AL x y).
    - exact (AR x y).
    - exact (last_glue x y).
  Defined.

  Definition associative_cd_s1_from_gaps : Associative mu
    := fun x y z => (associator x y z)^.

  (** Step 6: inverse uniqueness completes the doubled spheroid; double again and transfer to S7. This definition still has OPEN 2--5 as parameters. *)
  Definition hspace_s7_from_gaps : IsHSpace (psphere 7).
  Proof.
    pose proof associative_cd_s1_from_gaps.
    pose (spheroid3 := cd_spheroid_of_associative (X:=psphere 1)).
    napply (ishspace_equiv_hspace pequiv_iterated_join_s1_s7^-1*).
    nrefine (@hspace_cd (pjoin (psphere 1) (Sphere 1)) spheroid3 _ _).
    - exact _.
    - exact cd_diamond_double.
  Defined.
End Construction.
End S7ProofOutline.

(** ** Alternative rectangle-based criteria *)

(** The four scalar-corner lemmas [cd_associativity_rectangle_ll], [cd_associativity_rectangle_lr], [cd_associativity_rectangle_rl], and [cd_associativity_rectangle_rr] supply the point cases of double join induction, using [commutative_sgop_s1]. Extending these particular fillers still requires glue coherences. For example, the first glue case would be:
<<
  transport (cd_associativity_rectangle a b (joinl c)) (jglue d e)
    (cd_associativity_rectangle_ll a b c d)
  = cd_associativity_rectangle_lr a b c e
>>
This compares the chosen fillers, not merely their endpoints. No extension of these scalar-normalized choices across the glues is asserted. *)

(** Proof skeleton with its remaining obligation exposed as an argument, not an axiom. The required family is the rectangle comparison for the chosen circle double, with both later arguments arbitrary join elements. No inhabitant of this family is supplied here. *)
Definition hspace_s7_from_rectangle `{Univalence}
  (h : forall (a b : Sphere 1) (u v : Join (Sphere 1) (Sphere 1)),
    cd_associativity_rectangle (X:=psphere 1) a b u v)
  : IsHSpace (psphere 7).
Proof.
  (** 1. The rectangle family gives associativity of the first double. *)
  pose proof (cd_assoc_from_rectangle h).
  (** 2. Inverse uniqueness completes its spheroid structure. *)
  pose (spheroid3 := cd_spheroid_of_associative (X:=psphere 1)).
  (** 3. Double again with the directly constructed join diamond. *)
  napply (ishspace_equiv_hspace pequiv_iterated_join_s1_s7^-1*).
  nrefine (@hspace_cd (pjoin (psphere 1) (Sphere 1)) spheroid3 _ _).
  - exact _.
  - exact cd_diamond_double.
Defined.

(** Normalizing in the middle argument gives a different choice of corners. The families [cd_associativity_rectangle_middle_l] and [cd_associativity_rectangle_middle_r] are defined for every [v], so both inner glue coherences are supplied by [apD]. The remaining outer glue compatibility follows if transport around each middle rectangle fixes the specified unit filler. This is a sufficient condition, not a claim that such invariance has been proved. *)
Definition hspace_s7_from_rectangle_invariance `{Univalence}
  (h : forall (a b c d : Sphere 1) (v : Join (Sphere 1) (Sphere 1)),
    transport (fun u => cd_associativity_rectangle (X:=psphere 1) a b u v)
      (join_rectangle_loop (A:=psphere 1) (B:=psphere 1) c d)
      (cd_associativity_rectangle_unit a b v)
    = cd_associativity_rectangle_unit a b v)
  : IsHSpace (psphere 7).
Proof.
  napply hspace_s7_from_rectangle.
  intros a b u v.
  exact (Join_ind_from_rectangle (A:=psphere 1) (B:=psphere 1)
    (fun u => cd_associativity_rectangle a b u v)
    (cd_associativity_rectangle_unit a b v) (fun c d => h a b c d v) u).
Defined.
