From HoTT Require Import Basics.
Require Import Types.Arrow Types.Paths Types.Prod.
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

  (** Translate the complete recursion data at [(1,conj c * d)] by [c], including all four boundary witnesses. This definition acts on recursion data; identifying it with postcomposition of the original filler by [functor_join (.* c) (.* c)] is a separate functoriality comparison. *)
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

  (** The actual mixed filler agrees with the normalized recursion-data filler along these specified boundary paths. The two paths through the parameter use the equality above and dependent naturality of the same family [cd_diamond], never a reflected diamond. No equality with other choices of scalar boundary paths is asserted. *)
  Definition cd_op_diamond_normalize `{Funext} (a b c d : X)
    : let fl := fun x => cd_diamond_map_l a mon_unit x * c in
      let fr := fun y => cd_diamond_map_r b mon_unit y * c in
      let pf := path_arrow _ _ (cd_diamond_map_l_normalize a c) in
      let pg := path_arrow _ _ (cd_diamond_map_r_normalize b c) in
      let t := cd_diamond_parameter a b c d in
      let p_t := cd_diamond_parameter_normalize a b c d in
      let lt := ap10 pf t @ ap fl p_t in
      let rt := ap10 pg t @ ap fr p_t in
      let p := (cd_diamond_map_l_neg_unit a c)^ @ ap10 pf (-mon_unit)
        @ ap (.* c) (cd_diamond_map_l_neg_unit a mon_unit) in
      let q := (cd_diamond_map_l_parameter a b c d)^ @ lt
        @ ap (.* c) (cd_diamond_map_l_parameter a b mon_unit (conj c * d)) in
      let r := (cd_diamond_map_r_parameter a b c d)^ @ rt
        @ ap (.* c) (cd_diamond_map_r_parameter a b mon_unit (conj c * d)) in
      let s := (cd_diamond_map_r_unit b c)^ @ ap10 pg mon_unit
        @ ap (.* c) (cd_diamond_map_r_unit b mon_unit) in
      transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' p q) (path_prod' r s) (cd_op_diamond a b c d)
      = cd_op_diamond_normalized a b c d.
  Proof.
    exact (join_zigzag_filler_change (fun t => (cd_diamond t)^)
      (path_arrow _ _ (cd_diamond_map_l_normalize a c))
      (path_arrow _ _ (cd_diamond_map_r_normalize b c))
      (cd_diamond_parameter_normalize a b c d) _ _ _ _ _ _ _ _).
  Defined.

End SpheroidHSpace.

(** Resolve the inherited spheroid structure before searching for associativity. Ordinary instance search does not always unfold the inherited multiplication when matching the imaginaroid's associativity hypothesis. *)
#[export] Hint Extern 0 (IsHSpace (pjoin (psusp _) _))
  => rapply hspace_cd : typeclass_instances.

(** The original imaginaroid construction is the suspension instance of [hspace_cd]. *)
Notation hspace_cdi_susp_assoc := hspace_cd.
