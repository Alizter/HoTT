From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod.
Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
Require Import Classes.interfaces.abstract_algebra Classes.theory.groups.
Require Import Pointed.Core Pointed.pSusp.
Require Import Homotopy.HSpace.Core Homotopy.HSpace.Coherent.
Require Import Homotopy.Suspension.
Require Import Homotopy.Join.Core.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The Cayley-Dickson Construction *)

(** The Cayley-Dickson construction in homotopy type theory due to Buchholtz and Rijke https://arxiv.org/abs/1610.01134 is a method to construct an H-space structure on the join of two suspensions of a type [A]. As a special case, this gives a way to construct an H-space structure on [S^3] leading to the quaternionic Hopf fibration.

The construction works by replicating the classical Cayley-Dickson construction on convolution algebras ([*]-algebras), which can produce the complex numbers, quaternions, octonions, etc. starting with the real numbers. We cannot replicate this directly in HoTT since such algebras have a contractible underlying vector space, therefore the construction here attempts to axiomatize the properties of the units of those algebras instead.

This is done by postulating a structure called a "Cayley-Dickson imaginaroid" on a type [A] and showing that [Join (Susp A) (Susp A)] is an H-space. Here we separate the algebra from the geometry: an associative spheroid [X] with a chosen diamond gives an H-space on [Join X X], and suspensions supply the canonical diamond. We also prove the doubled involution, inverse, and sign laws, without additional coherences of the diamond. In fact, doubled negation is homotopic to the identity. We construct unit-based partial associators and give an explicit rectangle-loop comparison sufficient for their compatibility. Associativity of the doubled multiplication is not established here. Once it is supplied, inverse anti-multiplicativity completes the doubled spheroid structure, and the join supplies its next diamond directly. Recovering an imaginaroid on [Join A (Susp A)] remains an open problem requiring further coherences. *)

(** ** Cayley-Dickson spheroids *)

(** A Cayley-Dickson Spheroid is a pointed type X which is an H-space, with two operations called negation and conjugation, satisfying the following seven laws:
  1. [--x = x]
  2. [x** = x]
  3. [1* = 1]
  4. [(-x)* = -x*]
  5. [x(-y) = -(xy)]
  6. [(xy)* = y* x*]
  7. [x* x = 1]
Note that the above laws are written in pseudocode since we cannot define multiplication by juxtaposition in Coq, and * is used to denote conjugation. *)
Class CayleyDicksonSpheroid (X : pType) := {
  cds_hspace :: IsHSpace X;
  cds_negate :: Negate X;
  cds_conjug :: Conjugate X;
  cds_negate_inv :: Involutive cds_negate;
  cds_conjug_inv :: Involutive cds_conjug;
  cds_conjug_unit_pres :: IsUnitPreserving cds_conjug;
  cds_conjug_left_inv :: LeftInverse (.*.) cds_conjug mon_unit;
  cds_conjug_distr :: DistrOpp (.*.) cds_conjug;
  cds_swapop :: SwapOp (-) cds_conjug;
  cds_factorneg_r :: FactorNegRight (-) (.*.)
}.

Section CayleyDicksonSpheroid_Properties.

  Context {X : pType} `(CayleyDicksonSpheroid X).

  Local Instance isequiv_cds_conjug : IsEquiv cds_conjug
    := isequiv_adjointify cds_conjug cds_conjug cds_conjug_inv cds_conjug_inv.

  #[export] Instance cds_factorneg_l : FactorNegLeft (-) (.*.).
  Proof.
    intros x y.
    rapply (equiv_inj conj).
    lhs rapply distropp.
    rhs rapply swapop.
    rhs rapply (ap _ (distropp _ _)).
    rhs_V rapply factorneg_r.
    napply ap.
    apply swapop.
  Defined.

  #[export] Instance cds_conjug_right_inv : RightInverse (.*.) cds_conjug mon_unit.
  Proof.
    intro x.
    lhs_V exact (ap (.* conj x) (involutive x)).
    rapply left_inverse.
  Defined.

End CayleyDicksonSpheroid_Properties.

(** ** Chosen diamonds *)

(** The geometric input to doubling a spheroid is a chosen filler, not merely the assertion that a filler exists. We express it as an equality of zigzags, so the construction only needs path algebra. No multiplication or associativity is needed to state this data. Additional laws for the doubled multiplication can then be formulated as coherences of this choice. *)
Class CayleyDicksonDiamond (X : pType) (neg : X -> X)
  := cd_diamond : forall t : X,
    zigzag (neg pt) t pt = zigzag (neg pt) t t.

(** ** Negation and conjugation on suspensions *)

Instance conjugate_susp (A : Type) `(Negate A) : Conjugate (Susp A)
  := functor_susp (-).

Instance negate_susp (A : Type) `(Negate A) : Negate (Susp A)
  := susp_neg _ o conjugate_susp A (-).

(** [conjugate_susp A] and [negate_susp A] commute. *)
Instance swapop_conjugate_susp {A} `(Negate A)
  : SwapOp (negate_susp A (-)) (conjugate_susp A (-)).
Proof.
  intros x.
  symmetry.
  napply susp_neg_natural.
Defined.

(** [conjugate_susp A] is involutive, since any functor applied to an involution gives an involution. *)
Instance involutive_conjugate_susp {A} `(Negate A, !Involutive (-))
  : Involutive (conjugate_susp A (-)).
Proof.
  intros x.
  lhs_V napply functor_susp_compose.
  rhs_V napply functor_susp_idmap.
  napply functor2_susp.
  exact involutive.
Defined.

(** [conjugate_susp A] is involutive as any composite of commuting involutions is an involution. *)
Instance involutive_negate_susp {A} `(Negate A, !Involutive (-))
  : Involutive (negate_susp A (-)).
Proof.
  intros x.
  unfold negate_susp.
  lhs napply ap.
  1: napply swapop_conjugate_susp.
  lhs rapply susp_neg_inv.
  rapply involutive.
Defined.

(** Every suspension supplies a canonical diamond. Only the value of suspension negation at the north pole is used; no laws of the negation on [A], or multiplication on [Susp A], are needed. *)
Instance cd_diamond_susp {A : Type} `{Negate A}
  : CayleyDicksonDiamond (psusp A) (-)
  := Susp_ind (fun t => zigzag South t North = zigzag South t t)
       (diamond_v South North 1) (diamond_h North South 1)
       (fun a => diamond_twist (merid a)).

(** ** Cayley-Dickson imaginaroids *)

Class CayleyDicksonImaginaroid (A : Type) := {
  cdi_negate :: Negate A;
  cdi_negate_involutive :: Involutive cdi_negate;
  cdi_susp_hspace :: IsHSpace (psusp A);
  cdi_susp_factorneg_r :: FactorNegRight (negate_susp A cdi_negate) hspace_op;
  cdi_susp_conjug_left_inv :: LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit;
  cdi_susp_conjug_distr :: DistrOpp hspace_op (conjugate_susp A cdi_negate);
}.

Instance isunitpreserving_conjugate_susp {A} `(CayleyDicksonImaginaroid A)
  : @IsUnitPreserving _ _ pt pt (conjugate_susp A cdi_negate)
  := idpath.

(** Every suspension of a Cayley-Dickson imaginaroid gives a Cayley-Dickson spheroid. *)
Instance cds_susp_cdi {A} `(CayleyDicksonImaginaroid A)
  : CayleyDicksonSpheroid (psusp A) := {}.

Instance cdi_conjugate_susp_left_inverse {A} `(CayleyDicksonImaginaroid A)
  : LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  exact cds_conjug_left_inv.
Defined.

Instance cdi_conjugate_susp_right_inverse {A} `(CayleyDicksonImaginaroid A)
  : RightInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  stapply cds_conjug_right_inv.
Defined.

Instance cdi_susp_left_identity {A} `(CayleyDicksonImaginaroid A)
  : LeftIdentity hspace_op mon_unit
  := _.

Instance cdi_susp_right_identity {A} `(CayleyDicksonImaginaroid A)
  : RightIdentity hspace_op mon_unit
  := _.

Instance cdi_negate_susp_factornegleft {A} `(CayleyDicksonImaginaroid A)
  : FactorNegLeft (negate_susp A cdi_negate) hspace_op.
Proof.
  stapply cds_factorneg_l.
Defined.

(** ** Negation and conjugation on the double *)

Instance cd_negate {X : Type} `{Negate X} : Negate (Join X X)
  := functor_join (-) (-).

(** The next diamond is available on every double, independently of multiplication or a diamond on [X]. *)
#[export] Instance cd_diamond_double {X : pType} `{Negate X}
  : CayleyDicksonDiamond (pjoin X X) cd_negate
  := @diamond_join X X (-pt) pt pt.

Instance cd_conjugate {X : Type} `{Negate X, Conjugate X}
  : Conjugate (Join X X)
  := functor_join conj (-).

Instance involutive_cd_negate {X : Type}
  `{Negate X, !Involutive (-)} : Involutive cd_negate.
Proof.
  intro x.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_idmap.
  napply functor2_join; exact involutive.
Defined.

Instance involutive_cd_conjugate {X : Type}
  `{Negate X, Conjugate X, !Involutive (-), !Involutive conj}
  : Involutive cd_conjugate.
Proof.
  intro x.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_idmap.
  napply functor2_join; exact involutive.
Defined.

Instance swapop_cd {X : Type} `{Negate X, Conjugate X, !SwapOp (-) conj}
  : SwapOp cd_negate cd_conjugate.
Proof.
  intro x.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_compose.
  napply functor2_join.
  1: exact swapop.
  reflexivity.
Defined.

Instance isunitpreserving_cd_conjugate {X : pType}
  `{Negate X, Conjugate X, !@IsUnitPreserving X X pt pt conj}
  : @IsUnitPreserving (pjoin X X) (pjoin X X) pt pt cd_conjugate
  := ap joinl preserves_mon_unit.

(** The right-copy rotation has the quaternionic constructor table. We specify its glue directly, independently of multiplication or a chosen diamond. *)
Definition cd_chi {X : Type@{i}} `{Negate X, Conjugate X}
  : Join@{i i j} X X -> Join@{i i j} X X
  := Join_rec (joinr o conj) (fun b => joinl (-conj b))
       (fun a b => (jglue (-conj b) (conj a))^).

(** ** Multiplication on the double *)

(** An associative Cayley-Dickson spheroid with a chosen diamond gives an H-space structure on its self-join. For an imaginaroid, [cd_diamond_susp] supplies the diamond automatically. *)
Section SpheroidHSpace.

  Context {X : pType} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op} `{!CayleyDicksonDiamond X (-)}.

  (** These maps send the chosen diamond to the multiplication's mixed coherence. The suffixes [l] and [r] refer to the two join factors, not to left and right multiplication. *)
  Definition cd_diamond_map_l (a c : X) := fun x => a * (c * -x).
  Definition cd_diamond_map_r (b c : X) := fun y => c * (y * b).

  (** This is [functor_join (cd_diamond_map_l a c) (cd_diamond_map_r b c)], expressed via [Join_rec] to avoid an unused universe parameter. *)
  Definition cd_diamond_map (a b c : X) : Join X X -> Join X X
    := Join_rec (joinl o cd_diamond_map_l a c)
         (joinr o cd_diamond_map_r b c)
         (fun x y => jglue (cd_diamond_map_l a c x)
           (cd_diamond_map_r b c y)).

  Definition cd_diamond_parameter (a b c d : X)
    := conj c * conj a * d * conj b.

  Local Notation assoc := (simple_associativity (f:=hspace_op)).

  (** The four scalar boundary identifications for [cd_diamond_map]. *)
  Lemma cd_diamond_map_l_neg_unit (a c : X)
    : cd_diamond_map_l a c (- mon_unit) = a * c.
  Proof.
    exact (ap (fun x => a * (c * x)) (cds_negate_inv mon_unit)
      @ ap (a *.) (hspace_right_identity c)).
  Defined.

  Lemma cd_diamond_map_l_parameter (a b c d : X)
    : cd_diamond_map_l a c (cd_diamond_parameter a b c d) = (-d) * conj b.
  Proof.
    (** Move the sign out, then cancel [a * c] against its conjugate. *)
    refine (_ @ (factorneg_l d (conj b))^).
    refine (ap (a *.) (factorneg_r c _) @ factorneg_r a _ @ _).
    napply (ap (-)).
    refine (assoc a c _ @ assoc (a * c) _ (conj b) @ _).
    napply (ap (.* conj b)).
    refine (assoc (a * c) _ d @ _ @ left_identity d).
    napply (ap (.* d)).
    exact (ap ((a * c) *.) (distropp a c)^
      @ right_inverse (a * c)).
  Defined.

  Lemma cd_diamond_map_r_unit (b c : X)
    : cd_diamond_map_r b c mon_unit = c * b.
  Proof.
    exact (ap (c *.) (left_identity b)).
  Defined.

  Lemma cd_diamond_map_r_parameter (a b c d : X)
    : cd_diamond_map_r b c (cd_diamond_parameter a b c d) = conj a * d.
  Proof.
    pose (u := conj c * conj a * d).
    nrefine (concat (y:=c * u) _ _).
    - (** First cancel [conj b * b] on the right. *)
      refine (_ @ ap ((c * u) *.) (left_inverse b)
        @ right_identity (c * u)).
      refine (_ @ (assoc (c * u) (conj b) b)^).
      exact (assoc c (u * conj b) b
        @ ap (.* b) (assoc c u (conj b))).
    - (** Then cancel [c * conj c] on the left. *)
      refine (_ @ (assoc mon_unit (conj a) d)^
        @ left_identity (conj a * d)).
      refine (assoc c _ d @ ap (.* d) _).
      exact (assoc c (conj c) (conj a)
        @ ap (.* conj a) (right_inverse c)).
  Defined.

  (** The actual two-glue filler used by multiplication. Naming it exposes the chosen diamond to [Join_rec2_beta_jglue_jglue] without changing its boundary witnesses. *)
  Definition cd_op_diamond (a b c d : X)
    : zigzag (a * c) ((-d) * conj b) (conj a * d)
      = zigzag (a * c) ((-d) * conj b) (c * b)
    := join_zigzag_filler (cd_diamond_map_l a c) (cd_diamond_map_r b c)
         (cd_diamond_map_l_neg_unit a c)
         (cd_diamond_map_l_parameter a b c d)
         (cd_diamond_map_r_parameter a b c d)
         (cd_diamond_map_r_unit b c)
         (cd_diamond (cd_diamond_parameter a b c d))^.

  (** Here is the multiplication map in algebraic form: [(a,b) * (c,d) = (a * c - d * b*, a* * d + c * b)].  The following is the spherical form. *)
  #[export] Instance cd_op : SgOp (pjoin X X).
  Proof.
    snapply Join_rec2.
    - exact (fun a b => joinl (a * b)).
    - exact (fun a b => joinr (conj a * b)).
    - exact (fun a b => joinr (b * a)).
    - exact (fun a b => joinl ((- b) * conj a)).
    - intros; apply jglue.
    - intros; symmetry; apply jglue.
    - intros; apply jglue.
    - intros; symmetry; apply jglue.
    - exact cd_op_diamond.
  Defined.

  #[export] Instance cd_op_left_identity
    : LeftIdentity cd_op pt.
  Proof.
    snapply Join_ind_Flr.
    1: exact (fun _ => ap joinl (hspace_left_identity _)).
    1: exact (fun b => ap joinr
      (ap (.* b) cds_conjug_unit_pres @ hspace_left_identity b)).
    intros a b.
    lhs napply (Join_rec_beta_jglue _ _ _ a b @@ 1).
    symmetry.
    apply join_natsq.
  Defined.

  #[export] Instance cd_op_right_identity
    : RightIdentity cd_op pt.
  Proof.
    snapply Join_ind_Flr.
    1: exact (fun _ => ap joinl (hspace_right_identity _)).
    1: exact (fun _ => ap joinr (hspace_left_identity _)).
    intros a b.
    lhs napply (Join_rec_beta_jglue _ _ _ a b @@ 1).
    simpl; symmetry.
    apply join_natsq.
  Defined.

  (** Negation is left translation by the image of [-1]. The glue case uses only naturality of [jglue], not a comparison of diamond fillers. *)
  Definition cd_negate_translation
    : cd_op (joinl (-mon_unit)) == cd_negate.
  Proof.
    snapply Join_ind_FlFr.
    - intro a.
      exact (ap joinl (factorneg_l mon_unit a
        @ ap (-) (hspace_left_identity a))).
    - intro b.
      napply (ap joinr).
      refine (ap (.* b) _ @ _).
      1: exact (swapop mon_unit @ ap (-) cds_conjug_unit_pres).
      exact (factorneg_l mon_unit b
        @ ap (-) (hspace_left_identity b)).
    - intros a b.
      lhs napply (Join_rec_beta_jglue _ _ _ a b @@ 1).
      symmetry.
      lhs napply (1 @@ functor_join_beta_jglue (-) (-) a b).
      apply join_natsq.
  Defined.

  (** The points [joinl (-pt)] and [joinl pt] are connected through [joinr pt], even when [-pt] and [pt] are in different components of [X]. *)
  Definition cd_negate_homotopic_id (z : pjoin X X) : cd_negate z = z.
  Proof.
    exact ((cd_negate_translation z)^
      @ ap (fun w => cd_op w z) (zigzag (-pt) pt pt)
      @ cd_op_left_identity z).
  Defined.

  (** These are the sign laws as unstructured paths; no prescribed higher coherence of these witnesses is asserted. *)
  #[export] Instance cd_op_factorneg_r : FactorNegRight cd_negate cd_op.
  Proof.
    intros x y.
    exact (ap (cd_op x) (cd_negate_homotopic_id y)
      @ (cd_negate_homotopic_id (cd_op x y))^).
  Defined.

  #[export] Instance cd_op_factorneg_l : FactorNegLeft cd_negate cd_op.
  Proof.
    intros x y.
    exact (ap (fun z => cd_op z y) (cd_negate_homotopic_id x)
      @ (cd_negate_homotopic_id (cd_op x y))^).
  Defined.

  (** The diagonal inverse law only uses the one-glue computation rules. Its image is a zigzag with a common right vertex, so no symmetry of the chosen diamond is needed. *)
  #[export] Instance cd_op_conjugate_left_inverse
    : LeftInverse cd_op cd_conjugate pt.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinl (left_inverse a)).
    - intro b; exact (ap joinl (right_inverse (-b))).
    - intros a b.
      rhs napply (1 @@ ap_const _ _).
      rhs napply concat_p1.
      apply moveR_pM.
      rhs_V napply (ap_pV joinl).
      rhs_V napply (triangle_h' (B:=X) (conj (conj a) * b)).
      (** Compute the diagonal path by changing the second argument first. *)
      lhs_V napply (ap011_diag
        (fun x y => cd_op (cd_conjugate y) x) (jglue a b)).
      lhs napply (ap011_is_ap
        (fun x y => cd_op (cd_conjugate y) x)).
      napply concat2.
      + exact (Join_rec_beta_jglue _ _ _ a b).
      + lhs napply (ap_compose cd_conjugate
          (fun z => cd_op z (joinr b))).
        lhs napply (ap _ (functor_join_beta_jglue conj (-) a b)).
        exact (Join_rec_beta_jglue _ _ _ (conj a) (-b)).
  Defined.

  #[export] Instance cd_op_conjugate_right_inverse
    : RightInverse cd_op cd_conjugate pt.
  Proof.
    intro z.
    lhs_V exact (ap (fun w => cd_op w (cd_conjugate z))
      (involutive_cd_conjugate z)).
    apply cd_op_conjugate_left_inverse.
  Defined.

  #[export] Instance hspace_cd : IsHSpace (pjoin X X) := {}.

  (** The two unit witnesses agree after inclusion into the join, even when the scalar H-space has no chosen unit coherence. *)
  #[export] Instance iscoherent_cd : IsCoherent (pjoin X X).
  Proof.
    unfold IsCoherent.
    lhs_V rapply (triangle_h' (point X)).
    rhs_V rapply (triangle_h' (point X)).
    reflexivity.
  Defined.

  (** ** Associativity via rectangle loops *)

  (** The comparison at the unit, built from the chosen left-unit paths. *)
  Definition cd_assoc_at_unit (u v : pjoin X X)
    : cd_op (cd_op pt u) v = cd_op pt (cd_op u v)
    := ap (fun z => cd_op z v) (cd_op_left_identity u)
         @ (cd_op_left_identity (cd_op u v))^.

  (** Both partial associators use paths from the join factors to the unit. These choices need not agree with scalar-normalized associators at the corners. *)
  Definition cd_assoc_l (a : X) (u v : pjoin X X)
    : cd_op (cd_op (joinl a) u) v = cd_op (joinl a) (cd_op u v).
  Proof.
    pose (p := zigzag a (point X) (point X)).
    exact (ap (fun z => cd_op (cd_op z u) v) p
      @ cd_assoc_at_unit u v
      @ (ap (fun z => cd_op z (cd_op u v)) p)^).
  Defined.

  Definition cd_assoc_r (b : X) (u v : pjoin X X)
    : cd_op (cd_op (joinr b) u) v = cd_op (joinr b) (cd_op u v).
  Proof.
    pose (p := (jglue (point X) b)^).
    exact (ap (fun z => cd_op (cd_op z u) v) p
      @ cd_assoc_at_unit u v
      @ (ap (fun z => cd_op z (cd_op u v)) p)^).
  Defined.

  (** The remaining obligation for these partial associators. It must be supplied as a family in all four variables, not just at scalar vertices. *)
  Definition cd_associativity_rectangle (a b : X) (u v : pjoin X X)
    := ap (fun z => cd_op (cd_op z u) v) (join_rectangle_loop a b)
         @ cd_assoc_at_unit u v
       = cd_assoc_at_unit u v
         @ ap (fun z => cd_op z (cd_op u v)) (join_rectangle_loop a b).

  (** At the middle unit, the associator comes from the right and left unit laws. Naturality of the left unit and [iscoherent_cd] identify its value at the first unit with the specified [cd_assoc_at_unit]. *)
  Definition cd_associativity_rectangle_unit (a b : X) (v : pjoin X X)
    : cd_associativity_rectangle a b pt v.
  Proof.
    pose (h := fun z =>
      ap (fun w => cd_op w v) (cd_op_right_identity z)
        @ (ap (cd_op z) (cd_op_left_identity v))^).
    assert (q : h pt = cd_assoc_at_unit pt v).
    { unfold h, cd_assoc_at_unit.
      lhs napply (ap (ap (fun w => cd_op w v)) iscoherent_cd^ @@ 1).
      napply whiskerL; napply inverse2.
      napply (cancelR _ _ (cd_op_left_identity v)).
      exact (concat_A1p cd_op_left_identity (cd_op_left_identity v)). }
    unfold cd_associativity_rectangle.
    lhs_V napply (1 @@ q).
    rhs_V napply (q @@ 1).
    exact (concat_Ap h (join_rectangle_loop a b)).
  Defined.

  (** Normalize in the middle argument before choosing scalar corners. Each of these families is already defined for every last argument [v], so its glue coherences in [v] are given by [apD]. These are not asserted equal to the scalar-normalized corner fillers below. *)
  Definition cd_associativity_rectangle_middle_l
    (a b c : X) (v : pjoin X X)
    : cd_associativity_rectangle a b (joinl c) v
    := transport (fun u => cd_associativity_rectangle a b u v)
         (zigzag c (point X) (point X))^
         (cd_associativity_rectangle_unit a b v).

  Definition cd_associativity_rectangle_middle_r
    (a b c : X) (v : pjoin X X)
    : cd_associativity_rectangle a b (joinr c) v
    := transport (fun u => cd_associativity_rectangle a b u v)
         (jglue (point X) c)
         (cd_associativity_rectangle_unit a b v).

  (** This is conditional: no inhabitant of the rectangle-comparison family is constructed here. [Associative] uses the reverse orientation of [cd_assoc_l] and [cd_assoc_r]. *)
  Definition cd_assoc_from_rectangle
    (h : forall a b u v, cd_associativity_rectangle a b u v)
    : Associative cd_op.
  Proof.
    intros x u v.
    exact (Join_homotopy_from_rectangle
      (fun z => cd_op (cd_op z u) v)
      (fun z => cd_op z (cd_op u v))
      (cd_assoc_at_unit u v) (fun a b => h a b u v) x)^.
  Defined.

  (** Once doubled associativity is supplied, inverse anti-multiplicativity completes the spheroid structure. No independent coherence of conjugation is assumed. *)
  Definition cd_spheroid_of_associative `{!Associative cd_op}
    : CayleyDicksonSpheroid (pjoin X X).
  Proof.
    refine {| cds_hspace := hspace_cd;
              cds_negate := cd_negate;
              cds_conjug := cd_conjugate;
              cds_negate_inv := involutive_cd_negate;
              cds_conjug_inv := involutive_cd_conjugate;
              cds_conjug_unit_pres := isunitpreserving_cd_conjugate;
              cds_conjug_left_inv := cd_op_conjugate_left_inverse;
              cds_conjug_distr := _;
              cds_swapop := swapop_cd;
              cds_factorneg_r := cd_op_factorneg_r |}.
    intros x y.
    rapply (inverse_sg_op (op:=cd_op) (unit:=pt) (i:=cd_conjugate) x y).
  Defined.

  (** ** Associativity at scalar corners *)

  Context `{!Commutative (@hspace_op X _)}.

  Local Notation comm := (commutativity (f:=@hspace_op X _)).

  (** The subscripts refer to the second and third arguments; the first argument is an arbitrary join element. These homotopies use only one-glue computations, so they work for any chosen diamond. *)
  Definition cd_assoc_ll (c d : X)
    : forall z : pjoin X X,
      cd_op (cd_op z (joinl c)) (joinl d)
        = cd_op z (joinl (c * d)).
  Proof.
    pose (hl := fun a => (assoc a c d)^).
    pose (hr := fun b => assoc d c b
      @ ap (fun x => hspace_op x b) (comm d c)).
    snapply (Join_ind_FFlFr
      (fun z => cd_op z (joinl c)) (fun z => cd_op z (joinl d))
      (fun z => cd_op z (joinl (c * d)))).
    - intro a; exact (ap joinl (hl a)).
    - intro b; exact (ap joinr (hr b)).
    - intros a b.
      lhs napply (ap (ap (fun z => cd_op z (joinl d)))
        (Join_rec_beta_jglue _ _
          (fun a b => jglue (a * c) (c * b)) a b) @@ 1).
      lhs napply (Join_rec_beta_jglue _ _
        (fun x y => jglue (x * d) (d * y)) (a * c) (c * b) @@ 1).
      rhs napply (1 @@ Join_rec_beta_jglue _ _
        (fun x y => jglue (x * (c * d)) ((c * d) * y)) a b).
      exact (join_natsq (hl a) (hr b))^.
  Defined.

  Definition cd_assoc_lr (c d : X)
    : forall z : pjoin X X,
      cd_op (cd_op z (joinl c)) (joinr d)
        = cd_op z (joinr (conj c * d)).
  Proof.
    assert (hl : forall a, conj (a * c) * d = conj a * (conj c * d)).
    { intro a.
      refine (ap (.* d) (distropp a c) @ _).
      exact (ap (.* d) (comm (conj c) (conj a))
        @ (assoc (conj a) (conj c) d)^). }
    assert (hr : forall b, (-d) * conj (c * b) = (-(conj c * d)) * conj b).
    { intro b.
      refine (factorneg_l d _ @ _ @ (factorneg_l _ (conj b))^).
      napply (ap (-)).
      refine (ap (d *.) (distropp c b) @ _).
      refine (ap (d *.) (comm (conj b) (conj c)) @ _).
      exact (assoc d (conj c) (conj b)
        @ ap (.* conj b) (comm d (conj c))). }
    snapply (Join_ind_FFlFr
      (fun z => cd_op z (joinl c)) (fun z => cd_op z (joinr d))
      (fun z => cd_op z (joinr (conj c * d)))).
    - intro a; exact (ap joinr (hl a)).
    - intro b; exact (ap joinl (hr b)).
    - intros a b.
      lhs napply (ap (ap (fun z => cd_op z (joinr d)))
        (Join_rec_beta_jglue _ _
          (fun a b => jglue (a * c) (c * b)) a b) @@ 1).
      lhs napply (Join_rec_beta_jglue _ _
        (fun x y => (jglue ((-d) * conj y) (conj x * d))^)
        (a * c) (c * b) @@ 1).
      rhs napply (1 @@ Join_rec_beta_jglue _ _
        (fun x y => (jglue ((-(conj c * d)) * conj y)
          (conj x * (conj c * d)))^) a b).
      apply moveR_Vp.
      rhs napply concat_p_pp.
      apply moveL_pV.
      exact (join_natsq (hr b) (hl a)).
  Defined.

  Definition cd_assoc_rl (c d : X)
    : forall z : pjoin X X,
      cd_op (cd_op z (joinr c)) (joinl d)
        = cd_op z (joinr (d * c)).
  Proof.
    assert (hl : forall a, d * (conj a * c) = conj a * (d * c)).
    { intro a.
      refine (assoc d (conj a) c @ _).
      exact (ap (.* c) (comm d (conj a))
        @ (assoc (conj a) d c)^). }
    assert (hr : forall b, ((-c) * conj b) * d = (-(d * c)) * conj b).
    { intro b.
      refine (ap (.* d) (factorneg_l c (conj b)) @ _).
      refine (factorneg_l (c * conj b) d @ _ @ (factorneg_l _ (conj b))^).
      napply (ap (-)).
      refine (comm (c * conj b) d @ _).
      exact (assoc d c (conj b)). }
    snapply (Join_ind_FFlFr
      (fun z => cd_op z (joinr c)) (fun z => cd_op z (joinl d))
      (fun z => cd_op z (joinr (d * c)))).
    - intro a; exact (ap joinr (hl a)).
    - intro b; exact (ap joinl (hr b)).
    - intros a b.
      lhs napply (ap (ap (fun z => cd_op z (joinl d)))
        (Join_rec_beta_jglue _ _
          (fun a b => (jglue ((-c) * conj b) (conj a * c))^) a b) @@ 1).
      lhs napply (ap_V (fun z => cd_op z (joinl d)) _ @@ 1).
      lhs napply (inverse2 (Join_rec_beta_jglue _ _
        (fun x y => jglue (x * d) (d * y))
        ((-c) * conj b) (conj a * c)) @@ 1).
      rhs napply (1 @@ Join_rec_beta_jglue _ _
        (fun x y => (jglue ((-(d * c)) * conj y)
          (conj x * (d * c)))^) a b).
      apply moveR_Vp.
      rhs napply concat_p_pp.
      apply moveL_pV.
      exact (join_natsq (hr b) (hl a)).
  Defined.

  Definition cd_assoc_rr (c d : X)
    : forall z : pjoin X X,
      cd_op (cd_op z (joinr c)) (joinr d)
        = cd_op z (joinl ((-d) * conj c)).
  Proof.
    assert (hl : forall a, (-d) * conj (conj a * c) = a * ((-d) * conj c)).
    { intro a.
      refine (ap ((-d) *.) (distropp (conj a) c) @ _).
      refine (ap (fun x => (-d) * (conj c * x)) (cds_conjug_inv a) @ _).
      exact (assoc (-d) (conj c) a @ comm ((-d) * conj c) a). }
    assert (hr : forall b, conj ((-c) * conj b) * d = ((-d) * conj c) * b).
    { intro b.
      refine (ap (.* d) (distropp (-c) (conj b)) @ _).
      refine (ap (fun x => (x * conj (-c)) * d) (cds_conjug_inv b) @ _).
      refine (ap (fun x => (b * x) * d) (swapop c) @ _).
      refine (ap (.* d) (factorneg_r b (conj c)) @ _).
      refine (factorneg_l (b * conj c) d @ _).
      refine (_ @ ap (.* b) (factorneg_l d (conj c))^).
      refine (_ @ (factorneg_l (d * conj c) b)^).
      napply (ap (-)).
      refine (comm (b * conj c) d @ _).
      exact (ap (d *.) (comm b (conj c))
        @ assoc d (conj c) b). }
    snapply (Join_ind_FFlFr
      (fun z => cd_op z (joinr c)) (fun z => cd_op z (joinr d))
      (fun z => cd_op z (joinl ((-d) * conj c)))).
    - intro a; exact (ap joinl (hl a)).
    - intro b; exact (ap joinr (hr b)).
    - intros a b.
      lhs napply (ap (ap (fun z => cd_op z (joinr d)))
        (Join_rec_beta_jglue _ _
          (fun a b => (jglue ((-c) * conj b) (conj a * c))^) a b) @@ 1).
      lhs napply (ap_V (fun z => cd_op z (joinr d)) _ @@ 1).
      lhs napply (inverse2 (Join_rec_beta_jglue _ _
        (fun x y => (jglue ((-d) * conj y) (conj x * d))^)
        ((-c) * conj b) (conj a * c)) @@ 1).
      lhs napply (inv_V _ @@ 1).
      rhs napply (1 @@ Join_rec_beta_jglue _ _
        (fun x y => jglue (x * ((-d) * conj c))
          (((-d) * conj c) * y)) a b).
      exact (join_natsq (hl a) (hr b))^.
  Defined.

  Local Opaque cd_diamond cd_op_diamond.

  (** Associators with the first two arguments in specified copies and the last argument arbitrary. Their point clauses reuse the four scalar-corner associators above, including their chosen scalar witnesses. *)
  Definition cd_assoc_first_ll (a b : X)
    : forall z : pjoin X X, cd_op (cd_op (joinl a) (joinl b)) z
      = cd_op (joinl a) (cd_op (joinl b) z).
  Proof.
    snapply Join_ind_FlFr.
    - intro c; exact (cd_assoc_ll b c (joinl a)).
    - intro d; exact (cd_assoc_lr b d (joinl a)).
    - intros c d.
      lhs napply (Join_rec_beta_jglue _ _
        (fun c d => jglue ((a * b) * c) (conj (a * b) * d)) c d @@ 1).
      rhs napply (1 @@ ap_compose (cd_op (joinl b))
        (cd_op (joinl a)) (jglue c d)).
      rhs napply (1 @@ ap (ap (cd_op (joinl a)))
        (Join_rec_beta_jglue _ _
          (fun c d => jglue (b * c) (conj b * d)) c d)).
      rhs napply (1 @@ Join_rec_beta_jglue _ _
        (fun c d => jglue (a * c) (conj a * d)) (b * c) (conj b * d)).
      exact (join_natsq _ _)^.
  Defined.

  Definition cd_assoc_first_lr (a b : X)
    : forall z : pjoin X X, cd_op (cd_op (joinl a) (joinr b)) z
      = cd_op (joinl a) (cd_op (joinr b) z).
  Proof.
    snapply Join_ind_FlFr.
    - intro c; exact (cd_assoc_rl b c (joinl a)).
    - intro d; exact (cd_assoc_rr b d (joinl a)).
    - intros c d.
      lhs napply (Join_rec_beta_jglue _ _
        (fun c d => (jglue ((-d) * conj (conj a * b))
          (c * (conj a * b)))^) c d @@ 1).
      rhs napply (1 @@ ap_compose (cd_op (joinr b))
        (cd_op (joinl a)) (jglue c d)).
      rhs napply (1 @@ ap (ap (cd_op (joinl a)))
        (Join_rec_beta_jglue _ _
          (fun c d => (jglue ((-d) * conj b) (c * b))^) c d)).
      rhs napply (1 @@ ap_V (cd_op (joinl a))
        (jglue ((-d) * conj b) (c * b))).
      change (cd_op (joinl a)) with
        (Join_rec (fun c => joinl (a * c)) (fun d => joinr (conj a * d))
          (fun c d => jglue (a * c) (conj a * d))).
      rhs napply (1 @@ inverse2 (Join_rec_beta_jglue (P:=pjoin X X) _ _
        (fun c d => jglue (a * c) (conj a * d))
        ((-d) * conj b) (c * b))).
      exact (inverse_natural _ _ (join_natsq _ _)).
  Defined.

  Definition cd_assoc_first_rl (a b : X)
    : forall z : pjoin X X, cd_op (cd_op (joinr a) (joinl b)) z
      = cd_op (joinr a) (cd_op (joinl b) z).
  Proof.
    snapply Join_ind_FlFr.
    - intro c; exact (cd_assoc_ll b c (joinr a)).
    - intro d; exact (cd_assoc_lr b d (joinr a)).
    - intros c d.
      lhs napply (Join_rec_beta_jglue _ _
        (fun c d => (jglue ((-d) * conj (b * a))
          (c * (b * a)))^) c d @@ 1).
      rhs napply (1 @@ ap_compose (cd_op (joinl b))
        (cd_op (joinr a)) (jglue c d)).
      rhs napply (1 @@ ap (ap (cd_op (joinr a)))
        (Join_rec_beta_jglue _ _
          (fun c d => jglue (b * c) (conj b * d)) c d)).
      change (cd_op (joinr a)) with
        (Join_rec (fun c => joinr (c * a))
          (fun d => joinl ((-d) * conj a))
          (fun c d => (jglue ((-d) * conj a) (c * a))^)).
      rhs napply (1 @@ Join_rec_beta_jglue _ _
        (fun c d => (jglue ((-d) * conj a) (c * a))^)
        (b * c) (conj b * d)).
      exact (inverse_natural _ _ (join_natsq _ _)).
  Defined.

  Definition cd_assoc_first_rr (a b : X)
    : forall z : pjoin X X, cd_op (cd_op (joinr a) (joinr b)) z
      = cd_op (joinr a) (cd_op (joinr b) z).
  Proof.
    snapply Join_ind_FlFr.
    - intro c; exact (cd_assoc_rl b c (joinr a)).
    - intro d; exact (cd_assoc_rr b d (joinr a)).
    - intros c d.
      lhs napply (Join_rec_beta_jglue _ _
        (fun c d => jglue (((-b) * conj a) * c)
          (conj ((-b) * conj a) * d)) c d @@ 1).
      rhs napply (1 @@ ap_compose (cd_op (joinr b))
        (cd_op (joinr a)) (jglue c d)).
      rhs napply (1 @@ ap (ap (cd_op (joinr a)))
        (Join_rec_beta_jglue _ _
          (fun c d => (jglue ((-d) * conj b) (c * b))^) c d)).
      rhs napply (1 @@ ap_V (cd_op (joinr a))
        (jglue ((-d) * conj b) (c * b))).
      change (cd_op (joinr a)) with
        (Join_rec (fun c => joinr (c * a))
          (fun d => joinl ((-d) * conj a))
          (fun c d => (jglue ((-d) * conj a) (c * a))^)).
      rhs napply (1 @@ inverse2 (Join_rec_beta_jglue _ _
        (fun c d => (jglue ((-d) * conj a) (c * a))^)
        ((-d) * conj b) (c * b))).
      rhs napply (1 @@ inv_V _).
      exact (join_natsq _ _)^.
  Defined.

  Local Transparent cd_diamond cd_op_diamond.

  (** To obtain the specified rectangle comparison, we must also compare each corner homotopy at the unit with [cd_assoc_at_unit]. Both paths factor through the same join inclusion, whose path images are identified by the triangle lemmas. Thus no equality of scalar coherence witnesses is assumed. *)
  Definition cd_associativity_rectangle_ll (a b c d : X)
    : cd_associativity_rectangle a b (joinl c) (joinl d).
  Proof.
    assert (q : cd_assoc_ll c d pt = cd_assoc_at_unit (joinl c) (joinl d)).
    { rhs_V napply (ap_compose joinl (fun z => cd_op z (joinl d)) _ @@ 1).
      rhs napply (ap_compose (fun x => x * d) joinl _ @@ 1).
      rhs_V napply (ap_pV joinl).
      lhs_V rapply (triangle_h' (point X)).
      rhs_V rapply (triangle_h' (point X)).
      reflexivity. }
    unfold cd_associativity_rectangle.
    lhs_V napply (1 @@ q).
    rhs_V napply (q @@ 1).
    exact (concat_Ap (cd_assoc_ll c d) (join_rectangle_loop a b)).
  Defined.

  Definition cd_associativity_rectangle_lr (a b c d : X)
    : cd_associativity_rectangle a b (joinl c) (joinr d).
  Proof.
    assert (q : cd_assoc_lr c d pt = cd_assoc_at_unit (joinl c) (joinr d)).
    { rhs_V napply (ap_compose joinl (fun z => cd_op z (joinr d)) _ @@ 1).
      rhs napply (ap_compose (fun x => conj x * d) joinr _ @@ 1).
      rhs_V napply (ap_pV joinr).
      lhs_V rapply (triangle_v' (point X)).
      rhs_V rapply (triangle_v' (point X)).
      reflexivity. }
    unfold cd_associativity_rectangle.
    lhs_V napply (1 @@ q).
    rhs_V napply (q @@ 1).
    exact (concat_Ap (cd_assoc_lr c d) (join_rectangle_loop a b)).
  Defined.

  Definition cd_associativity_rectangle_rl (a b c d : X)
    : cd_associativity_rectangle a b (joinr c) (joinl d).
  Proof.
    assert (q : cd_assoc_rl c d pt = cd_assoc_at_unit (joinr c) (joinl d)).
    { rhs_V napply (ap_compose joinr (fun z => cd_op z (joinl d)) _ @@ 1).
      rhs napply (ap_compose (fun x => d * x) joinr _ @@ 1).
      rhs_V napply (ap_pV joinr).
      lhs_V rapply (triangle_v' (point X)).
      rhs_V rapply (triangle_v' (point X)).
      reflexivity. }
    unfold cd_associativity_rectangle.
    lhs_V napply (1 @@ q).
    rhs_V napply (q @@ 1).
    exact (concat_Ap (cd_assoc_rl c d) (join_rectangle_loop a b)).
  Defined.

  Definition cd_associativity_rectangle_rr (a b c d : X)
    : cd_associativity_rectangle a b (joinr c) (joinr d).
  Proof.
    assert (q : cd_assoc_rr c d pt = cd_assoc_at_unit (joinr c) (joinr d)).
    { rhs_V napply (ap_compose joinr (fun z => cd_op z (joinr d)) _ @@ 1).
      rhs napply (ap_compose (fun x => (-d) * conj x) joinl _ @@ 1).
      rhs_V napply (ap_pV joinl).
      lhs_V rapply (triangle_h' (point X)).
      rhs_V rapply (triangle_h' (point X)).
      reflexivity. }
    unfold cd_associativity_rectangle.
    lhs_V napply (1 @@ q).
    rhs_V napply (q @@ 1).
    exact (concat_Ap (cd_assoc_rr c d) (join_rectangle_loop a b)).
  Defined.

  (** ** Scalar right translations *)

  (** Right multiplication by a left-copy scalar is the diagonal join map. The scalar commutativity path on the right copy and its naturality are retained. *)
  Definition cd_op_right_translate_joinl (r : X)
    : forall z : pjoin X X,
      cd_op z (joinl r) = functor_join (.* r) (.* r) z.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; reflexivity.
    - intro b; exact (ap joinr (comm r b)).
    - intros a b.
      lhs napply (Join_rec_beta_jglue _ _
        (fun a b => jglue (a * r) (r * b)) a b @@ 1).
      rhs napply (1 @@ functor_join_beta_jglue (.* r) (.* r) a b).
      exact (join_natsq 1 (comm r b))^.
  Defined.

  Local Opaque cd_diamond cd_op_diamond.

  (** Right multiplication by a right-copy scalar is diagonal translation after [cd_chi]. This retains the negation and commutativity witnesses on the right constructor. *)
  Definition cd_op_right_translate_joinr (r : X)
    : forall z : pjoin X X,
      cd_op z (joinr r) = functor_join (.* r) (.* r) (cd_chi z).
  Proof.
    pose (p := fun b : X => factorneg_l r (conj b)
      @ ap (-) (comm r (conj b)) @ (factorneg_l (conj b) r)^).
    snapply Join_ind_FlFr.
    - reflexivity.
    - intro b; exact (ap joinl (p b)).
    - intros a b.
      lhs napply (Join_rec_beta_jglue _ _
        (fun a b => (jglue ((-r) * conj b) (conj a * r))^) a b @@ 1).
      rhs napply (1 @@ ap_compose cd_chi
        (functor_join (.* r) (.* r)) (jglue a b)).
      rhs napply (1 @@ ap (ap (functor_join (.* r) (.* r)))
        (Join_rec_beta_jglue _ _
          (fun a b => (jglue (-conj b) (conj a))^) a b)).
      rhs napply (1 @@ ap_V (functor_join (.* r) (.* r))
        (jglue (-conj b) (conj a))).
      rhs napply (1 @@ inverse2 (functor_join_beta_jglue (.* r) (.* r)
        (-conj b) (conj a))).
      exact (inverse_natural _ _ (join_natsq (p b) 1)).
  Defined.

  (** The unit join glue connects right multiplication by the two unit constructors. Together with the specified translations and right unit paths, it supplies an explicit homotopy from [cd_chi] to the identity. No reflection law for the chosen diamond is needed. *)
  Definition cd_chi_homotopic_id (z : pjoin X X) : cd_chi z = z.
  Proof.
    refine ((cd_op_right_identity (cd_chi z))^ @ _).
    refine (cd_op_right_translate_joinl mon_unit (cd_chi z) @ _).
    refine ((cd_op_right_translate_joinr mon_unit z)^ @ _).
    exact (ap (cd_op z) (jglue mon_unit mon_unit)^ @ cd_op_right_identity z).
  Defined.

  (** This is a full symmetry homotopy with the choice induced by the unit join glue. In particular, its faces are not silently identified with a different choice obtained from scalar-normalized reflected diamonds. Compatibility with diagonal equivariance remains a separate question. *)
  Definition cd_op_chi_equivariance (x y : pjoin X X)
    : cd_op x (cd_chi y) = cd_chi (cd_op x y)
    := ap (cd_op x) (cd_chi_homotopic_id y)
      @ (cd_chi_homotopic_id (cd_op x y))^.

  Local Transparent cd_diamond cd_op_diamond.

  (** ** Diagonal-translation normal form *)

  (** The parameter is unchanged by replacing [(c,d)] with [(1,conj c * d)]. This uses commutativity of the scalar multiplication, but no property of the chosen diamond. *)
  Definition cd_diamond_parameter_normalize (a b c d : X)
    : cd_diamond_parameter a b c d
      = cd_diamond_parameter a b mon_unit (conj c * d).
  Proof.
    unfold cd_diamond_parameter.
    rhs rapply (ap (fun x => x * (conj c * d) * conj b)
      (ap (.* conj a) cds_conjug_unit_pres @ left_identity (conj a))).
    napply (ap (.* conj b)).
    exact (ap (.* d) (comm (conj c) (conj a))
      @ (assoc (conj a) (conj c) d)^).
  Defined.

  Definition cd_diamond_map_l_normalize (a c : X)
    : cd_diamond_map_l a c == fun x => cd_diamond_map_l a mon_unit x * c.
  Proof.
    intro x; unfold cd_diamond_map_l.
    rhs rapply (ap (.* c) (ap (a *.) (left_identity (-x)))).
    exact (ap (a *.) (comm c (-x)) @ assoc a (-x) c).
  Defined.

  Definition cd_diamond_map_r_normalize (b c : X)
    : cd_diamond_map_r b c == fun y => cd_diamond_map_r b mon_unit y * c.
  Proof.
    intro y; unfold cd_diamond_map_r.
    rhs rapply (ap (.* c) (left_identity (y * b))).
    exact (comm c (y * b)).
  Defined.

  (** In particular, diagonal translation of the second glue does not change the diamond argument. *)
  Definition cd_diamond_parameter_translate (a b c d r : X)
    : cd_diamond_parameter a b (c * r) (d * r)
      = cd_diamond_parameter a b c d.
  Proof.
    refine (cd_diamond_parameter_normalize a b (c * r) (d * r) @ _).
    refine (_ @ (cd_diamond_parameter_normalize a b c d)^).
    napply (ap (cd_diamond_parameter a b mon_unit)).
    refine (ap (.* (d * r)) (distropp c r) @ _).
    refine (ap (.* (d * r)) (comm (conj r) (conj c)) @ _).
    refine ((assoc (conj c) (conj r) (d * r))^ @ _).
    napply (ap (conj c *.)).
    refine (ap (conj r *.) (comm d r) @ _).
    refine (assoc (conj r) r d @ _).
    exact (ap (.* d) (left_inverse r) @ left_identity d).
  Defined.

  (** Translate the complete recursion data at [(1,conj c * d)] by [c], including all four boundary witnesses. By [join_zigzag_filler_compose], this is also the complete filler obtained by postcomposition with the diagonal join map. *)
  Definition cd_op_diamond_normalized (a b c d : X)
    : zigzag ((a * mon_unit) * c) (((-(conj c * d)) * conj b) * c)
        ((conj a * (conj c * d)) * c)
      = zigzag ((a * mon_unit) * c) (((-(conj c * d)) * conj b) * c)
        ((mon_unit * b) * c)
    := join_zigzag_filler
         (fun x => cd_diamond_map_l a mon_unit x * c)
         (fun y => cd_diamond_map_r b mon_unit y * c)
         (ap (.* c) (cd_diamond_map_l_neg_unit a mon_unit))
         (ap (.* c) (cd_diamond_map_l_parameter a b mon_unit (conj c * d)))
         (ap (.* c) (cd_diamond_map_r_parameter a b mon_unit (conj c * d)))
         (ap (.* c) (cd_diamond_map_r_unit b mon_unit))
         (cd_diamond (cd_diamond_parameter a b mon_unit (conj c * d)))^.

  (** The actual mixed filler agrees with postcomposition of the unit-normalized filler along these specified boundary paths. The two paths through the parameter use the equality above and dependent naturality of the same family [cd_diamond], never a reflected diamond. No equality with other choices of scalar boundary paths is asserted. *)
  Definition cd_op_diamond_normalize (a b c d : X)
    : let fl := fun x => cd_diamond_map_l a mon_unit x * c in
      let fr := fun y => cd_diamond_map_r b mon_unit y * c in
      let pf := cd_diamond_map_l_normalize a c in
      let pg := cd_diamond_map_r_normalize b c in
      let t := cd_diamond_parameter a b c d in
      let p_t := cd_diamond_parameter_normalize a b c d in
      let lt := pf t @ ap fl p_t in
      let rt := pg t @ ap fr p_t in
      let p := (cd_diamond_map_l_neg_unit a c)^ @ pf (-mon_unit)
        @ ap (.* c) (cd_diamond_map_l_neg_unit a mon_unit) in
      let q := (cd_diamond_map_l_parameter a b c d)^ @ lt
        @ ap (.* c) (cd_diamond_map_l_parameter a b mon_unit (conj c * d)) in
      let r := (cd_diamond_map_r_parameter a b c d)^ @ rt
        @ ap (.* c) (cd_diamond_map_r_parameter a b mon_unit (conj c * d)) in
      let s := (cd_diamond_map_r_unit b c)^ @ pg mon_unit
        @ ap (.* c) (cd_diamond_map_r_unit b mon_unit) in
      transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' p q) (path_prod' r s) (cd_op_diamond a b c d)
      = join_zigzag_filler (.* c) (.* c) 1 1 1 1
          (cd_op_diamond a b mon_unit (conj c * d)).
  Proof.
    cbn zeta.
    rhs napply (join_zigzag_filler_compose
      (cd_diamond_map_l a mon_unit) (cd_diamond_map_r b mon_unit)
      (.* c) (.* c)).
    exact (join_zigzag_filler_change (fun t => (cd_diamond t)^)
      (cd_diamond_map_l_normalize a c)
      (cd_diamond_map_r_normalize b c)
      (cd_diamond_parameter_normalize a b c d) _ _ _ _ _ _ _ _).
  Defined.

  (** ** Diagonal translation of the mixed filler *)

  Definition cd_diamond_map_l_translate (a c r : X)
    : cd_diamond_map_l a (c * r)
      == fun x => cd_diamond_map_l a c x * r.
  Proof.
    intro x.
    refine (cd_diamond_map_l_normalize a (c * r) x @ _).
    refine (assoc (cd_diamond_map_l a mon_unit x) c r @ _).
    exact (ap (.* r) (cd_diamond_map_l_normalize a c x)^).
  Defined.

  Definition cd_diamond_map_r_translate (b c r : X)
    : cd_diamond_map_r b (c * r)
      == fun y => cd_diamond_map_r b c y * r.
  Proof.
    intro y.
    refine (cd_diamond_map_r_normalize b (c * r) y @ _).
    refine (assoc (cd_diamond_map_r b mon_unit y) c r @ _).
    exact (ap (.* r) (cd_diamond_map_r_normalize b c y)^).
  Defined.

  (** These are the boundary paths induced by translating the same diamond. Naming them keeps their choices explicit when comparing the multiplication's recursion data. *)
  Definition cd_diamond_translate_l_neg_unit (a c r : X)
    : a * (c * r) = (a * c) * r
    := (cd_diamond_map_l_neg_unit a (c * r))^
      @ cd_diamond_map_l_translate a c r (-mon_unit)
      @ ap (.* r) (cd_diamond_map_l_neg_unit a c).

  Definition cd_diamond_translate_l_parameter (a b c d r : X)
    : (-(d * r)) * conj b = ((-d) * conj b) * r.
  Proof.
    nrefine (_ @ ap (.* r) (cd_diamond_map_l_parameter a b c d)).
    nrefine ((cd_diamond_map_l_parameter a b (c * r) (d * r))^ @ _).
    exact (cd_diamond_map_l_translate a c r
        (cd_diamond_parameter a b (c * r) (d * r))
      @ ap (fun x => cd_diamond_map_l a c x * r)
          (cd_diamond_parameter_translate a b c d r)).
  Defined.

  Definition cd_diamond_translate_r_parameter (a b c d r : X)
    : conj a * (d * r) = (conj a * d) * r.
  Proof.
    nrefine (_ @ ap (.* r) (cd_diamond_map_r_parameter a b c d)).
    nrefine ((cd_diamond_map_r_parameter a b (c * r) (d * r))^ @ _).
    exact (cd_diamond_map_r_translate b c r
        (cd_diamond_parameter a b (c * r) (d * r))
      @ ap (fun y => cd_diamond_map_r b c y * r)
          (cd_diamond_parameter_translate a b c d r)).
  Defined.

  Definition cd_diamond_translate_r_unit (b c r : X)
    : (c * r) * b = (c * b) * r
    := (cd_diamond_map_r_unit b (c * r))^
      @ cd_diamond_map_r_translate b c r mon_unit
      @ ap (.* r) (cd_diamond_map_r_unit b c).

  (** This is a comparison of the actual fillers, with all four induced boundary paths. There is no reflection or replacement of [cd_diamond]. *)
  Definition cd_op_diamond_translate (a b c d r : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (cd_diamond_translate_l_neg_unit a c r)
          (cd_diamond_translate_l_parameter a b c d r))
        (path_prod' (cd_diamond_translate_r_parameter a b c d r)
          (cd_diamond_translate_r_unit b c r))
        (cd_op_diamond a b (c * r) (d * r))
      = join_zigzag_filler (.* r) (.* r) 1 1 1 1 (cd_op_diamond a b c d).
  Proof.
    rhs napply (join_zigzag_filler_compose
      (cd_diamond_map_l a c) (cd_diamond_map_r b c) (.* r) (.* r)).
    exact (join_zigzag_filler_change (fun t => (cd_diamond t)^)
      (cd_diamond_map_l_translate a c r)
      (cd_diamond_map_r_translate b c r)
      (cd_diamond_parameter_translate a b c d r) _ _ _ _ _ _ _ _).
  Defined.

  (** The first-variable point clauses for diagonal equivariance. Their four scalar paths are exactly the vertex paths used in [cd_op_diamond_diagonal] below. *)
  Definition cd_op_diagonal_equivariance_joinl (r a : X)
    : forall y : pjoin X X,
      cd_op (joinl a) (functor_join (.* r) (.* r) y)
        = functor_join (.* r) (.* r) (cd_op (joinl a) y).
  Proof.
    snapply Join_ind_FlFr.
    - intro c; exact (ap joinl (cd_diamond_translate_l_neg_unit a c r)).
    - intro d.
      exact (ap joinr
        (cd_diamond_translate_r_parameter a mon_unit mon_unit d r)).
    - intros c d.
      lhs napply (ap_compose (functor_join (.* r) (.* r))
        (cd_op (joinl a)) (jglue c d) @@ 1).
      lhs napply (ap (ap (cd_op (joinl a)))
        (functor_join_beta_jglue (.* r) (.* r) c d) @@ 1).
      change (cd_op (joinl a)) with
        (Join_rec (fun c => joinl (a * c)) (fun d => joinr (conj a * d))
          (fun c d => jglue (a * c) (conj a * d))).
      lhs napply (Join_rec_beta_jglue _ _
        (fun c d => jglue (a * c) (conj a * d)) (c * r) (d * r) @@ 1).
      rhs napply (1 @@ ap_compose (cd_op (joinl a))
        (functor_join (.* r) (.* r)) (jglue c d)).
      rhs napply (1 @@ ap (ap (functor_join (.* r) (.* r)))
        (Join_rec_beta_jglue (P:=pjoin X X)
          (fun c => joinl (a * c)) (fun d => joinr (conj a * d))
          (fun c d => jglue (a * c) (conj a * d)) c d)).
      rhs napply (1 @@ functor_join_beta_jglue (.* r) (.* r)
        (a * c) (conj a * d)).
      exact (join_natsq (cd_diamond_translate_l_neg_unit a c r)
        (cd_diamond_translate_r_parameter a mon_unit mon_unit d r))^.
  Defined.

  Definition cd_op_diagonal_equivariance_joinr (r b : X)
    : forall y : pjoin X X,
      cd_op (joinr b) (functor_join (.* r) (.* r) y)
        = functor_join (.* r) (.* r) (cd_op (joinr b) y).
  Proof.
    snapply Join_ind_FlFr.
    - intro c; exact (ap joinr (cd_diamond_translate_r_unit b c r)).
    - intro d.
      exact (ap joinl
        (cd_diamond_translate_l_parameter mon_unit b mon_unit d r)).
    - intros c d.
      lhs napply (ap_compose (functor_join (.* r) (.* r))
        (cd_op (joinr b)) (jglue c d) @@ 1).
      lhs napply (ap (ap (cd_op (joinr b)))
        (functor_join_beta_jglue (.* r) (.* r) c d) @@ 1).
      lhs napply (Join_rec_beta_jglue _ _
        (fun c d => (jglue ((-d) * conj b) (c * b))^) (c * r) (d * r) @@ 1).
      rhs napply (1 @@ ap_compose (cd_op (joinr b))
        (functor_join (.* r) (.* r)) (jglue c d)).
      rhs napply (1 @@ ap (ap (functor_join (.* r) (.* r)))
        (Join_rec_beta_jglue _ _
          (fun c d => (jglue ((-d) * conj b) (c * b))^) c d)).
      rhs napply (1 @@ ap_V (functor_join (.* r) (.* r))
        (jglue ((-d) * conj b) (c * b))).
      rhs napply (1 @@ inverse2 (functor_join_beta_jglue (.* r) (.* r)
        ((-d) * conj b) (c * b))).
      apply moveL_pV.
      lhs napply concat_pp_p.
      apply moveR_Vp.
      exact (join_natsq
        (cd_diamond_translate_l_parameter mon_unit b mon_unit d r)
        (cd_diamond_translate_r_unit b c r)).
  Defined.

  (** The two point clauses for the first-variable glue of equivariance, using the same four vertex paths as the point homotopies above. *)
  Definition cd_op_diagonal_equivariance_glue_joinl (r a b c : X)
    : ap (fun x => cd_op x (joinl (c * r))) (jglue a b)
        @ cd_op_diagonal_equivariance_joinr r b (joinl c)
      = cd_op_diagonal_equivariance_joinl r a (joinl c)
        @ ap (fun x => functor_join (.* r) (.* r) (cd_op x (joinl c)))
            (jglue a b).
  Proof.
    lhs napply (Join_rec_beta_jglue _ _
      (fun a b => jglue (a * (c * r)) ((c * r) * b)) a b @@ 1).
    rhs napply (1 @@ ap_compose (fun x => cd_op x (joinl c))
      (functor_join (.* r) (.* r)) (jglue a b)).
    rhs napply (1 @@ ap (ap (functor_join (.* r) (.* r)))
      (Join_rec_beta_jglue _ _ (fun a b => jglue (a * c) (c * b)) a b)).
    rhs napply (1 @@ functor_join_beta_jglue (.* r) (.* r) (a * c) (c * b)).
    exact (join_natsq (cd_diamond_translate_l_neg_unit a c r)
      (cd_diamond_translate_r_unit b c r))^.
  Defined.

  Definition cd_op_diagonal_equivariance_glue_joinr (r a b d : X)
    : ap (fun x => cd_op x (joinr (d * r))) (jglue a b)
        @ cd_op_diagonal_equivariance_joinr r b (joinr d)
      = cd_op_diagonal_equivariance_joinl r a (joinr d)
        @ ap (fun x => functor_join (.* r) (.* r) (cd_op x (joinr d)))
            (jglue a b).
  Proof.
    lhs napply (Join_rec_beta_jglue _ _
      (fun a b => (jglue ((-(d * r)) * conj b) (conj a * (d * r)))^)
      a b @@ 1).
    rhs napply (1 @@ ap_compose (fun x => cd_op x (joinr d))
      (functor_join (.* r) (.* r)) (jglue a b)).
    rhs napply (1 @@ ap (ap (functor_join (.* r) (.* r)))
      (Join_rec_beta_jglue _ _
        (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b)).
    rhs napply (1 @@ ap_V (functor_join (.* r) (.* r))
      (jglue ((-d) * conj b) (conj a * d))).
    rhs napply (1 @@ inverse2 (functor_join_beta_jglue (.* r) (.* r)
      ((-d) * conj b) (conj a * d))).
    apply moveL_pV.
    lhs napply concat_pp_p.
    apply moveR_Vp.
    exact (join_natsq
      (cd_diamond_translate_l_parameter mon_unit b mon_unit d r)
      (cd_diamond_translate_r_parameter a mon_unit mon_unit d r)).
  Defined.

  (** For connected 1-truncated scalars, the parameter-corner paths are independent of the labels absent from their endpoints. Each such scalar-path family is set-valued, so connectedness gives a nullhomotopy. We normalize it by its value at [mon_unit], rather than identifying its arbitrary center with the chosen unit value. The resulting comparisons at the unit cancel to reflexivity. No truncation of the join-valued fillers is used. *)
  Context `{!IsConnected (0%trunc) X, !IsTrunc 1 X}.

  Definition cd_diamond_translate_l_parameter_independent (a b c d r : X)
    : cd_diamond_translate_l_parameter a b c d r
      = cd_diamond_translate_l_parameter mon_unit b mon_unit d r.
  Proof.
    destruct (isconnected_elim (Tr 0) _
      (fun x => cd_diamond_translate_l_parameter x b c d r)) as [p hp].
    nrefine (hp a @ _).
    nrefine ((hp mon_unit)^ @ _).
    destruct (isconnected_elim (Tr 0) _
      (fun x => cd_diamond_translate_l_parameter mon_unit b x d r)) as [q hq].
    exact (hq c @ (hq mon_unit)^).
  Defined.

  Definition cd_diamond_translate_r_parameter_independent (a b c d r : X)
    : cd_diamond_translate_r_parameter a b c d r
      = cd_diamond_translate_r_parameter a mon_unit mon_unit d r.
  Proof.
    destruct (isconnected_elim (Tr 0) _
      (fun x => cd_diamond_translate_r_parameter a x c d r)) as [p hp].
    nrefine (hp b @ _).
    nrefine ((hp mon_unit)^ @ _).
    destruct (isconnected_elim (Tr 0) _
      (fun x => cd_diamond_translate_r_parameter a mon_unit x d r)) as [q hq].
    exact (hq c @ (hq mon_unit)^).
  Defined.

  (** After these scalar comparisons, each vertex path depends only on its own two input labels and the translation parameter. This is the boundary-aware mixed comparison for the proposed diagonal equivariance. *)
  Definition cd_op_diamond_diagonal (a b c d r : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (cd_diamond_translate_l_neg_unit a c r)
          (cd_diamond_translate_l_parameter mon_unit b mon_unit d r))
        (path_prod' (cd_diamond_translate_r_parameter a mon_unit mon_unit d r)
          (cd_diamond_translate_r_unit b c r))
        (cd_op_diamond a b (c * r) (d * r))
      = join_zigzag_filler (.* r) (.* r) 1 1 1 1 (cd_op_diamond a b c d).
  Proof.
    lhs_V napply (ap011 (fun p q => transport011 _ p q
      (cd_op_diamond a b (c * r) (d * r)))
      (ap (path_prod' (cd_diamond_translate_l_neg_unit a c r))
        (cd_diamond_translate_l_parameter_independent a b c d r))
      (ap (fun p => path_prod' p (cd_diamond_translate_r_unit b c r))
        (cd_diamond_translate_r_parameter_independent a b c d r))).
    exact (cd_op_diamond_translate a b c d r).
  Defined.

  (** Convert the transported mixed-filler comparison to the dependent mixed case of equivariance. The four existing side faces are compared using their actual beta paths, not replaced by faces with the same endpoints. *)
  Local Opaque cd_diamond cd_op_diamond.

  Definition cd_op_diagonal_equivariance_glue_glue (r a b c d : X)
    : transport
        (fun y => ap (fun x => cd_op x (functor_join (.* r) (.* r) y))
            (jglue a b) @ cd_op_diagonal_equivariance_joinr r b y
          = cd_op_diagonal_equivariance_joinl r a y
            @ ap (fun x => functor_join (.* r) (.* r) (cd_op x y))
                (jglue a b))
        (jglue c d) (cd_op_diagonal_equivariance_glue_joinl r a b c)
      = cd_op_diagonal_equivariance_glue_joinr r a b d.
  Proof.
    pose (rho := functor_join (.* r) (.* r)).
    pose (f0 := cd_op (joinl a)).
    pose (f1 := cd_op (joinr b)).
    pose (W := fun y => ap (fun x => cd_op x y) (jglue a b)).
    pose (U := fun y => W (rho y)).
    pose (V := fun y => ap (fun x => rho (cd_op x y)) (jglue a b)).
    (** First name the original four edge computations and the diagonal map's computation. *)
    pose (brho := functor_join_beta_jglue (.* r) (.* r)).
    pose (bh0 := fun c d => Join_rec_beta_jglue _ _
      (fun c d => jglue (a * c) (conj a * d)) c d).
    pose (bh1 := fun c d => Join_rec_beta_jglue _ _
      (fun c d => (jglue ((-d) * conj b) (c * b))^) c d).
    pose (bv0 := fun c => Join_rec_beta_jglue _ _
      (fun a b => jglue (a * c) (c * b)) a b).
    pose (bv1 := fun d => Join_rec_beta_jglue _ _
      (fun a b => (jglue ((-d) * conj b) (conj a * d))^) a b).
    (** The eight edge computations of multiplication before and after translation. *)
    pose (bfh0 := (ap_compose rho f0 (jglue c d)
      @ ap (ap f0) (brho c d)) @ bh0 (c * r) (d * r)).
    pose (bfh1 := (ap_compose rho f1 (jglue c d)
      @ ap (ap f1) (brho c d)) @ bh1 (c * r) (d * r)).
    pose (bfv0 := bv0 (c * r)).
    pose (bfv1 := bv1 (d * r)).
    pose (t := fun y => ap_compose (fun x => cd_op x y) rho (jglue a b)).
    pose (bgh0 := (ap_compose f0 rho (jglue c d)
      @ ap (ap rho) (bh0 c d)) @ brho (a * c) (conj a * d)).
    pose (bgh1 := (ap_compose f1 rho (jglue c d)
      @ ap (ap rho) (bh1 c d)) @ (ap_V rho (jglue ((-d) * conj b) (c * b))
        @ inverse2 (brho ((-d) * conj b) (c * b)))).
    pose (bgv0 := (t (joinl c) @ ap (ap rho) (bv0 c))
      @ brho (a * c) (c * b)).
    pose (bgv1 := (t (joinr d) @ ap (ap rho) (bv1 d))
      @ (ap_V rho (jglue ((-d) * conj b) (conj a * d))
        @ inverse2 (brho ((-d) * conj b) (conj a * d)))).
    (** Obtain both mixed computations from the named beta rule of the unchanged multiplication. *)
    assert (BM : forall c d, concat_Ap W (jglue c d) @ (bv0 c @@ 1)
      = (1 @@ bv1 d) @ naturality_change
          (bh0 c d) (bh1 c d) (cd_op_diamond a b c d)).
    { intros c0 d0.
      nrefine (Join_rec2_beta_jglue_jglue (pjoin X X)
        _ _ _ _ _ _ _ _ cd_op_diamond a b c0 d0 @ _).
      exact (1 @@ concat_p_pp _ _ _). }
    assert (BF : concat_Ap U (jglue c d) @ (bfv0 @@ 1)
      = (1 @@ bfv1) @ naturality_change bfh0 bfh1
        (cd_op_diamond a b (c * r) (d * r))).
    { exact (concat_Ap_precompose_beta W rho (jglue c d)
        (jglue (c * r) (d * r)) (brho c d)
        (bh0 (c * r) (d * r)) (bv1 (d * r))
        (bv0 (c * r)) (bh1 (c * r) (d * r)) _ (BM (c * r) (d * r))). }
    assert (BG : concat_Ap V (jglue c d) @ (bgv0 @@ 1)
      = (1 @@ bgv1) @ naturality_change bgh0 bgh1
        (join_zigzag_filler (.* r) (.* r) 1 1 1 1 (cd_op_diamond a b c d))).
    { napply (mixed_beta_compose
        (ap_compose f0 rho (jglue c d) @ ap (ap rho) (bh0 c d))
        (t (joinr d) @ ap (ap rho) (bv1 d))
        (t (joinl c) @ ap (ap rho) (bv0 c))
        (ap_compose f1 rho (jglue c d) @ ap (ap rho) (bh1 c d))
        _ _ _ _ _ (ap_naturality rho (cd_op_diamond a b c d)) _).
      - napply (mixed_beta_vertical (t (joinl c)) (t (joinr d))
          (ap (ap rho) (bv0 c)) (ap (ap rho) (bv1 d)) _ _
          _ (concat_Ap (fun y => ap rho (W y)) (jglue c d)) _).
        + exact (concat_Ap_homotopic V (fun y => ap rho (W y)) t (jglue c d)).
        + exact (concat_Ap_postcompose_beta W rho (jglue c d)
            (bh0 c d) (bv1 d) (bv0 c) (bh1 c d) _ (BM c d)).
      - rhs napply (1 @@ ap (naturality_change _ _)
          (join_zigzag_filler_refl (.* r) (.* r) (cd_op_diamond a b c d))).
        exact (ap_pV_filler_beta rho
          (jglue (a * c) (conj a * d)) (jglue ((-d) * conj b) (conj a * d))
          (jglue (a * c) (c * b)) (jglue ((-d) * conj b) (c * b))
          (brho _ _) (brho _ _) (brho _ _) (brho _ _) (cd_op_diamond a b c d)). }
    (** Match the four specified side faces to these edge computations. No scalar path or face witness is discarded. *)
    pose (p00 := cd_diamond_translate_l_neg_unit a c r).
    pose (p01 := cd_diamond_translate_r_parameter a mon_unit mon_unit d r).
    pose (p10 := cd_diamond_translate_r_unit b c r).
    pose (p11 := cd_diamond_translate_l_parameter mon_unit b mon_unit d r).
    pose (eh0 := (join_natsq p00 p01)^).
    pose (eh1 := inverse_natural _ _ (join_natsq p11 p10)).
    pose (ev0 := (join_natsq p00 p10)^).
    pose (ev1 := inverse_natural _ _ (join_natsq p11 p01)).
    assert (EH0 : concat_Ap (cd_op_diagonal_equivariance_joinl r a) (jglue c d)
      = naturality_change bfh0 bgh0 eh0).
    { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
      lhs napply naturality_prefix.
      lhs napply naturality_prefix.
      rhs napply concat_pp_p.
      napply (ap (fun q => (bfh0 @@ 1) @ q)).
      lhs napply naturality_suffix.
      apply naturality_suffix. }
    assert (EH1 : concat_Ap (cd_op_diagonal_equivariance_joinr r b) (jglue c d)
      = naturality_change bfh1 bgh1 eh1).
    { lhs napply (Join_ind_FlFr_beta_jglue _ _ _ _ _ c d).
      lhs napply naturality_prefix.
      lhs napply naturality_prefix.
      rhs napply concat_pp_p.
      napply (ap (fun q => (bfh1 @@ 1) @ q)).
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      exact (ap (fun q => eh1 @ (1 @@ q)^) (concat_pp_p _ _ _)). }
    assert (EV0 : cd_op_diagonal_equivariance_glue_joinl r a b c
      = naturality_change bfv0 bgv0 ev0).
    { rhs napply concat_pp_p.
      napply (ap (fun q => (bfv0 @@ 1) @ q)).
      lhs napply naturality_suffix.
      apply naturality_suffix. }
    assert (EV1 : cd_op_diagonal_equivariance_glue_joinr r a b d
      = naturality_change bfv1 bgv1 ev1).
    { rhs napply concat_pp_p.
      napply (ap (fun q => (bfv1 @@ 1) @ q)).
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      lhs napply naturality_suffix.
      exact (ap (fun q => ev1 @ (1 @@ q)^) (concat_pp_p _ _ _)). }
    (** The dependent glue equation is now the cube supplied by [cd_op_diamond_diagonal]. *)
    nrefine (equiv_naturality_transport2 _ _ (jglue c d) _ _ _).
    lhs napply (concat_Ap_concat U
      (cd_op_diagonal_equivariance_joinr r b) (jglue c d) @@ 1).
    rhs napply (1 @@ concat_Ap_concat
      (cd_op_diagonal_equivariance_joinl r a) V (jglue c d)).
    lhs napply (ap (concat_natural
      (ap (f0 o rho) (jglue c d)) (ap (f1 o rho) (jglue c d))
      (ap (rho o f1) (jglue c d)) (U (joinl c)) (U (joinr d))
      (ap joinr p10) (ap joinl p11) (concat_Ap U (jglue c d))) EH1 @@ 1).
    lhs napply (1 @@ ap (fun q => q @@ idpath (ap (rho o f1) (jglue c d))) EV0).
    rhs napply (ap (fun q => idpath (ap (f0 o rho) (jglue c d)) @@ q) EV1 @@ 1).
    rhs napply (1 @@ ap (fun q => concat_natural
      (ap (f0 o rho) (jglue c d)) (ap (rho o f0) (jglue c d))
      (ap (rho o f1) (jglue c d)) (ap joinl p00) (ap joinr p01)
      (V (joinl c)) (V (joinr d)) q (concat_Ap V (jglue c d))) EH0).
    napply (naturality_cube_change
      (ap joinl p00) (ap joinr p01) (ap joinr p10) (ap joinl p11)
      bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
      _ _ _ _ eh0 eh1 ev0 ev1 BF BG).
    exact (join_zigzag_filler_cube p00 p11 p01 p10 _ _
      (cd_op_diamond_diagonal a b c d r)).
  Defined.

  Local Transparent cd_diamond cd_op_diamond.

  Definition cd_op_diagonal_equivariance_glue (r a b : X)
    : forall y : pjoin X X,
      ap (fun x => cd_op x (functor_join (.* r) (.* r) y)) (jglue a b)
        @ cd_op_diagonal_equivariance_joinr r b y
      = cd_op_diagonal_equivariance_joinl r a y
        @ ap (fun x => functor_join (.* r) (.* r) (cd_op x y)) (jglue a b).
  Proof.
    snapply Join_ind.
    - exact (cd_op_diagonal_equivariance_glue_joinl r a b).
    - exact (cd_op_diagonal_equivariance_glue_joinr r a b).
    - exact (cd_op_diagonal_equivariance_glue_glue r a b).
  Defined.

  (** Full diagonal equivariance, with the existing point homotopies and the chosen dependent mixed computation. *)
  Definition cd_op_diagonal_equivariance (r : X)
    : forall x y : pjoin X X,
      cd_op x (functor_join (.* r) (.* r) y)
        = functor_join (.* r) (.* r) (cd_op x y).
  Proof.
    intros x y; revert x.
    snapply Join_ind_FlFr.
    - exact (fun a => cd_op_diagonal_equivariance_joinl r a y).
    - exact (fun b => cd_op_diagonal_equivariance_joinr r b y).
    - exact (fun a b => cd_op_diagonal_equivariance_glue r a b y).
  Defined.

  (** Equivariance and scalar right translation give the associator with a last argument in the left copy. Both preceding arguments remain arbitrary join elements. *)
  Definition cd_assoc_last_joinl (x y : pjoin X X) (r : X)
    : cd_op (cd_op x y) (joinl r) = cd_op x (cd_op y (joinl r))
    := cd_op_right_translate_joinl r (cd_op x y)
      @ (cd_op_diagonal_equivariance r x y)^
      @ ap (cd_op x) (cd_op_right_translate_joinl r y)^.

  (** Transport the fixed left associator to a right constructor. The second scalar is the variable of the resulting map into a fixed path type. *)
  Definition cd_assoc_last_transport (x y : pjoin X X) (d c : X)
    : cd_op (cd_op x y) (joinr d) = cd_op x (cd_op y (joinr d))
    := transport (fun z => cd_op (cd_op x y) z = cd_op x (cd_op y z))
         (jglue c d) (cd_assoc_last_joinl x y c).

  (** This alternative right partial associator makes the whole boundary [jglue mon_unit d] automatic. It changes neither multiplication nor the chosen left associator. No comparison with the symmetry-based right associator at arbitrary [d] is asserted. *)
  Definition cd_assoc_last_joinr_transport (x y : pjoin X X) (d : X)
    : cd_op (cd_op x y) (joinr d) = cd_op x (cd_op y (joinr d))
    := cd_assoc_last_transport x y d mon_unit.

  (** Compare the actual left associator with the first-two-constructor associators. Join triangles compare the images of the scalar witnesses; no equality of arbitrary scalar witnesses or join-valued fillers is assumed. *)
  Local Opaque cd_diamond cd_op_diamond.

  Definition cd_assoc_last_joinl_first_ll (a b c : X)
    : cd_assoc_last_joinl (joinl a) (joinl b) c
      = cd_assoc_first_ll a b (joinl c).
  Proof.
    lhs napply concat_p1.
    lhs napply concat_1p.
    lhs_V napply (ap_V (joinl (B:=X))
      (cd_diamond_translate_l_neg_unit a b c)).
    exact ((triangle_h' (point X)
        (cd_diamond_translate_l_neg_unit a b c)^)^
      @ triangle_h' (point X) (assoc a b c)^).
  Defined.

  Definition cd_assoc_last_joinl_first_lr (a b c : X)
    : cd_assoc_last_joinl (joinl a) (joinr b) c
      = cd_assoc_first_lr a b (joinl c).
  Proof.
    lhs_V napply (1 @@ ap (ap (cd_op (joinl a)))
      (ap_V (joinr (A:=X)) (comm c b))).
    lhs_V napply (1 @@ ap_compose joinr (cd_op (joinl a)) (comm c b)^).
    lhs napply (1 @@ ap_compose (conj a *.) joinr (comm c b)^).
    lhs_V napply (ap_pV (joinr (A:=X)) _ _ @@ 1).
    lhs_V napply (ap_pp (joinr (A:=X)) _ _).
    lhs_V rapply (triangle_v' (point X)).
    rhs_V rapply (triangle_v' (point X)).
    reflexivity.
  Defined.

  Definition cd_assoc_last_joinl_first_rl (a b c : X)
    : cd_assoc_last_joinl (joinr a) (joinl b) c
      = cd_assoc_first_rl a b (joinl c).
  Proof.
    lhs napply concat_p1.
    lhs_V napply (ap_pV (joinr (A:=X)) _ _).
    lhs_V rapply (triangle_v' (point X)).
    rhs_V rapply (triangle_v' (point X)).
    reflexivity.
  Defined.

  Definition cd_assoc_last_joinl_first_rr (a b c : X)
    : cd_assoc_last_joinl (joinr a) (joinr b) c
      = cd_assoc_first_rr a b (joinl c).
  Proof.
    lhs napply (concat_1p _ @@ 1).
    lhs_V napply (1 @@ ap (ap (cd_op (joinr a)))
      (ap_V (joinr (A:=X)) (comm c b))).
    lhs_V napply (1 @@ ap_compose joinr (cd_op (joinr a)) (comm c b)^).
    lhs napply (1 @@ ap_compose (fun d => (-d) * conj a) joinl (comm c b)^).
    lhs_V napply (ap_V (joinl (B:=X))
      (cd_diamond_translate_l_parameter mon_unit a mon_unit b c) @@ 1).
    lhs_V napply (ap_pp (joinl (B:=X)) _ _).
    lhs_V rapply (triangle_h' (point X)).
    rhs_V rapply (triangle_h' (point X)).
    reflexivity.
  Defined.

  (** Scalar loops vanish at each of the four constructor pairs of the preceding arguments. Each proof is a family in [d], so its second-label coherence is [apD]. Extending these proofs across the preceding arguments' join glues is still required; this is not loop vanishing for arbitrary join elements. *)
  Definition cd_assoc_last_transport_loop_ll (a b d : X)
    {c : X} (p : c = c)
    : ap (cd_assoc_last_transport (joinl a) (joinl b) d) p = 1.
  Proof.
    pose (K := fun c => ap (transport _ (jglue c d))
      (cd_assoc_last_joinl_first_ll a b c)
      @ apD (cd_assoc_first_ll a b) (jglue c d)).
    lhs napply (ap_homotopic K p).
    lhs napply ((1 @@ ap_const p _) @@ 1).
    lhs napply (concat_p1 _ @@ 1).
    apply concat_pV.
  Defined.

  Definition cd_assoc_last_transport_loop_lr (a b d : X)
    {c : X} (p : c = c)
    : ap (cd_assoc_last_transport (joinl a) (joinr b) d) p = 1.
  Proof.
    pose (K := fun c => ap (transport _ (jglue c d))
      (cd_assoc_last_joinl_first_lr a b c)
      @ apD (cd_assoc_first_lr a b) (jglue c d)).
    lhs napply (ap_homotopic K p).
    lhs napply ((1 @@ ap_const p _) @@ 1).
    lhs napply (concat_p1 _ @@ 1).
    apply concat_pV.
  Defined.

  Definition cd_assoc_last_transport_loop_rl (a b d : X)
    {c : X} (p : c = c)
    : ap (cd_assoc_last_transport (joinr a) (joinl b) d) p = 1.
  Proof.
    pose (K := fun c => ap (transport _ (jglue c d))
      (cd_assoc_last_joinl_first_rl a b c)
      @ apD (cd_assoc_first_rl a b) (jglue c d)).
    lhs napply (ap_homotopic K p).
    lhs napply ((1 @@ ap_const p _) @@ 1).
    lhs napply (concat_p1 _ @@ 1).
    apply concat_pV.
  Defined.

  Definition cd_assoc_last_transport_loop_rr (a b d : X)
    {c : X} (p : c = c)
    : ap (cd_assoc_last_transport (joinr a) (joinr b) d) p = 1.
  Proof.
    pose (K := fun c => ap (transport _ (jglue c d))
      (cd_assoc_last_joinl_first_rr a b c)
      @ apD (cd_assoc_first_rr a b) (jglue c d)).
    lhs napply (ap_homotopic K p).
    lhs napply ((1 @@ ap_const p _) @@ 1).
    lhs napply (concat_p1 _ @@ 1).
    apply concat_pV.
  Defined.

  Local Transparent cd_diamond cd_op_diamond.

  (** The chosen symmetry homotopy and diagonal equivariance give a last-right associator. This does not assert its compatibility with [cd_assoc_last_joinl] along the last join glue. *)
  Definition cd_assoc_last_joinr (x y : pjoin X X) (r : X)
    : cd_op (cd_op x y) (joinr r) = cd_op x (cd_op y (joinr r)).
  Proof.
    nrefine (cd_op_right_translate_joinr r (cd_op x y) @ _).
    nrefine (ap (functor_join (.* r) (.* r)) (cd_op_chi_equivariance x y)^ @ _).
    exact ((cd_op_diagonal_equivariance r x (cd_chi y))^
      @ ap (cd_op x) (cd_op_right_translate_joinr r y)^).
  Defined.

  (** The chosen last-left and last-right associators agree across the unit join glue, with both preceding arguments arbitrary. The comparison across [jglue c d] for arbitrary scalars remains a further coherence obligation. *)
  Definition cd_assoc_last_glue_unit (x y : pjoin X X)
    : transport (fun z => cd_op (cd_op x y) z = cd_op x (cd_op y z))
        (jglue (point X) (point X)) (cd_assoc_last_joinl x y mon_unit)
      = cd_assoc_last_joinr x y mon_unit.
  Proof.
    exact (transport_translation_comparison (joinl (point X)) cd_op
      cd_op_right_identity (functor_join (.* mon_unit) (.* mon_unit))
      (cd_op_right_translate_joinl mon_unit) (cd_op x)
      (fun y => cd_op_diagonal_equivariance mon_unit x y) y
      (jglue (point X) (point X)) (cd_chi y) (cd_chi (cd_op x y))
      (cd_op_right_translate_joinr mon_unit y)
      (cd_op_right_translate_joinr mon_unit (cd_op x y))).
  Defined.

End SpheroidHSpace.

(** Resolve the inherited spheroid structure before searching for associativity. Ordinary instance search does not always unfold the inherited multiplication when matching the imaginaroid's associativity hypothesis. *)
#[export] Hint Extern 0 (IsHSpace (pjoin (psusp _) _))
  => rapply hspace_cd : typeclass_instances.

(** The original imaginaroid construction is the suspension instance of [hspace_cd]. *)
Notation hspace_cdi_susp_assoc := hspace_cd.
