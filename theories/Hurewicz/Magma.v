Require Import Basics Types Pointed.
Require Import Algebra.Group.
Require Import EquivalenceVarieties.
Require Import Truncations.
Require Import PathAny.
Require Import Tactics.
Import TrM.

(* We use these two idioms several times.  When proving two records are
   equal, we convert to elements of sigma types and use path_sigma to
   reduce to goals involving the components.  Assumes only two components
   in the record, for now. *)
Ltac record_equality :=
  simple refine ((equiv_ap' _^-1 _ _)^-1 _); [ | issig | ];
  simple refine (path_sigma _ _ _ _ _); simpl.

(* Use this one if the fibers are known to be HProps. *)
Ltac record_equality_hprop :=
  simple refine ((equiv_ap' _^-1 _ _)^-1 _); [ | issig | ];
  apply path_sigma_hprop; simpl.

Record Magma := {
  magma_type :> Type;
  magma_op :> SgOp magma_type;
}.

Existing Instance magma_op.

Definition issig_magma : _ <~> Magma := ltac:(issig).

Record MagmaMap (X Y : Magma) := {
  magmamap_map :> X -> Y;
  magmamap_op_preserving : IsSemiGroupPreserving magmamap_map;
}.

Existing Instance magmamap_op_preserving.

Definition issig_magmamap X Y : _ <~> MagmaMap X Y := ltac:(issig).

(** TODO make more global anyway *)
Existing Instance compose_sg_morphism.

Definition magmamap_compose {X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) : MagmaMap X Z.
Proof.
  (* Typeclass resolution finds [compose_sg_morphism], which uses rewrite. *)
  apply (Build_MagmaMap _ _ (f o g)).
  red. intros x0 x1.
  simple refine ((ap f _) @ _).
  2: apply magmamap_op_preserving.
  apply magmamap_op_preserving.
Defined.

Definition magmamap_compose_assoc `{Funext} {W X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) (h : MagmaMap W X)
  : magmamap_compose (magmamap_compose f g) h = magmamap_compose f (magmamap_compose g h).
Proof.
  record_equality.
  - reflexivity.
  - apply path_forall2; intros w0 w1.
    refine (concat_p_pp _ _ _ @ _).
    apply whiskerR.
    refine (_ @ _).
    2: symmetry; apply ap_pp.
    apply whiskerR.
    apply ap_compose.
Defined.

Definition path_magmamap_hset `{Funext} {X Y : Magma} {f g : MagmaMap X Y}
  `{IsHSet Y}
  : f == g -> f = g.
Proof.
  intro p.
  record_equality_hprop.
  by apply path_forall.
Defined.

Record MagmaEquiv (X Y : Magma) := {
  magmamap :> MagmaMap X Y;
  magmamap_isequiv : IsEquiv (magmamap_map _ _ magmamap);
}.

Arguments magmamap {X Y} _.
Arguments magmamap_isequiv {X Y} _.

Definition issig_magmaequiv X Y : _ <~> MagmaEquiv X Y := ltac:(issig).

Definition magmaequiv_to_equiv {X Y : Magma} : MagmaEquiv X Y -> Equiv X Y
  := fun f => Build_Equiv _ _ f (magmamap_isequiv f).

Coercion magmaequiv_to_equiv : MagmaEquiv >-> Equiv.

Definition build_magmaequiv {X Y : Magma} (f : X -> Y) (e : IsEquiv f)
           (r : IsSemiGroupPreserving f) : MagmaEquiv X Y
  := (Build_MagmaEquiv X Y (Build_MagmaMap X Y f r) e).

Definition path_magmaequiv `{Funext} {X Y : Magma} (f g : MagmaEquiv X Y)
  : (magmamap f = magmamap g) <~> (f = g).
Proof.
  refine (_^-1 oE _).
  - apply (equiv_ap' (issig_magmaequiv _ _)^-1).
  - simpl.
    exact (equiv_path_sigma_hprop (magmamap f; magmamap_isequiv f) (magmamap g; magmamap_isequiv g)).
Defined.

Definition magma_idmap (X : Magma) : MagmaEquiv X X.
Proof.
  refine (build_magmaequiv idmap _ _).
  unfold IsSemiGroupPreserving.  reflexivity.
Defined.

Definition magmamap_compose_f1 `{Funext} {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose f (magma_idmap X) = f.
Proof.
  record_equality.
  - reflexivity.
  - apply path_forall2; intros x0 x1.
    apply concat_1p.
Defined.

Definition magmamap_compose_1f `{Funext} {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose (magma_idmap Y) f = f.
Proof.
  record_equality.
  - reflexivity.
  - apply path_forall2; intros x0 x1.
    refine (_ @ _).
    1:apply concat_p1.
    apply ap_idmap.
Defined.

Definition magmaequiv_compose {X Y Z : Magma} (g : MagmaEquiv Y Z) (f : MagmaEquiv X Y)
  : MagmaEquiv X Z.
Proof.
  (* Typeclass resolution finds [compose_sg_morphism], which uses rewrite. *)
  simple notypeclasses refine (build_magmaequiv (g oE f) _ _).
  - apply equiv_isequiv.
  - apply magmamap_compose.
Defined.

Definition magmaequiv_inverse {X Y : Magma} (f : MagmaEquiv X Y) : MagmaEquiv Y X.
Proof.
  (* Typeclass resolution uses [invert_sg_morphism], which uses rewrite. *)
  simple notypeclasses refine (build_magmaequiv (magmaequiv_to_equiv f)^-1 _ _).
  - apply equiv_isequiv.
  - apply isequiv_inverse.
  - red. intros y0 y1.
    (* Using [equiv_inj] here instead of [(ap (magmaequiv_to_equiv f))^-1]
       allows us to avoid unfolding it later until the right moment. *)
    refine (Paths.equiv_inj (magmaequiv_to_equiv f) _).
    refine (_ @ _ @ _ @ _)^.
    + exact (preserves_sg_op _ _).
    (* We could use [apply ap2; apply eisretr] here, but later it is convenient
       to have things in terms of ap. *)
    + refine (ap (fun y => sg_op y _) _); apply eisretr.
    + refine (ap (sg_op y0) _); apply eisretr.
    + symmetry; apply eisretr.
Defined.

(* The left inverse law.  Much trickier than I expected.  Would be easier with univalence. *)
Definition mecompose_eV `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_compose f (magmaequiv_inverse f) = magma_idmap _.
Proof.
  destruct f as [[f r] e].
  record_equality_hprop.
  change (magmamap_map X Y (Build_MagmaMap X Y f r)) with f in *.
  record_equality.
  + apply path_forall; intro; apply eisretr.
  + unfold preserves_sg_op.
    apply path_forall2; intros y0 y1.
    rewrite transport_forall_constant.
    rewrite transport_forall_constant.
    transport_path_forall_hammer.
    (* The key to making this proof simple was to avoid equiv_inj getting
       unfolded into (ap f)^-1 which would get reduced to a complicated
       expression by simpl/cbn.  We unfold it to (ap f)^-1 now, where it
       cancels against the adjacent (ap f): *)
    unfold equiv_inj.
    rewrite (eisretr (ap f)).
    rewrite @transport_paths_l.
    do 2 rewrite @transport_paths_Fr.
    rewrite inv_pV.
    do 2 rewrite inv_pp.
    do 6 rewrite concat_pp_p.
    do 3 rewrite concat_V_pp.
    apply concat_Vp.
Defined.

(* Every magma equivalence f has a right inverse f^-1.  So f^-1 has
   both left and right inverses.  It follows that
   (f^-1)^-1 = (f f^-1) (f^-1)^-1 = f (f^-1 (f^-1)^-1) = f. *)
Definition magmaequiv_inverse_inverse `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_inverse (magmaequiv_inverse f) = f.
Proof.
  apply path_magmaequiv.
  pose (fi := (magmaequiv_inverse f)).
  pose (fii := (magmaequiv_inverse fi)).
  refine (_^ @ _^ @ _ @ _ @ _).
  - exact (magmamap_compose_1f fii).
  - exact (ap (fun k => magmamap_compose (magmamap k) fii) (mecompose_eV f)).
  - apply magmamap_compose_assoc.
  - exact (ap (fun k => magmamap_compose f (magmamap k)) (mecompose_eV fi )).
  - apply magmamap_compose_f1.
Defined.

(* The right inverse law.  Proving this directly requires different
   path algebra than mecompose_eV, so we prove it indirectly. *)
Definition mecompose_Ve `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_compose (magmaequiv_inverse f) f = magma_idmap _.
Proof.
  refine (_ @ _).
  - exact (ap _ (magmaequiv_inverse_inverse f)^).
  - apply mecompose_eV.
Defined.

(* This should be in Overture.v, and path_forall2 should be defined in terms of this. *)
Definition equiv_path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y)
  : (forall (a : A) (b : B), f a b = g a b) <~> f = g
  := (equiv_path_forall f g) oE (equiv_functor_forall_id (fun a => equiv_path_forall (f a) (g a))).

(* Alternatively, one can prove that the existing path_forall2 is an equivalence: *)
Global Instance isequiv_path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y)
  : IsEquiv (path_forall2 f g).
Proof.
  unfold path_forall2.
  simple refine (isequiv_compose' _ _ (path_forall f g) _).
  apply (isequiv_functor_forall (f:=equiv_idmap) (g:=fun a => path_forall (f a) (g a))).
Defined.

(* With the second approach, need: *)
Definition equiv_path_forall2' `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y)
  := Build_Equiv _ _ (path_forall2 f g) _.

(* This is a drop-in replacement for contr_basedequiv in Universe.v.
   Coq is unable to compute the center of contraction with the proof
   given there, so we reprove it a different way.  I think this proof
   should replace that proof. *)
Global Instance contr_basedequiv_fix `{Univalence} {X : Type}
: Contr {Y : Type & X <~> Y}.
Proof.
  exists (X; equiv_idmap).
  intros [Y f]; revert Y f.
  apply equiv_induction.
  reflexivity.
Defined.

Definition issig_magmaequiv' (X Y : Magma) :
  {f : X <~> Y & IsSemiGroupPreserving f} <~> MagmaEquiv X Y.
Proof.
  serapply equiv_adjointify.
  - intros [[f e] r]; exact (build_magmaequiv f e r).
  - intros [[f r] e]; exact ((Build_Equiv _ _ f e); r).
  - simpl. reflexivity.
  - simpl. reflexivity.
Defined.

(* This verifies that we have the right notion of equivalence of magmas. *)
Definition equiv_magmaequiv_path `{Univalence} (X Y : Magma)
  : MagmaEquiv X Y <~> (X = Y).
Proof.
  refine (_ oE (issig_magmaequiv' X Y)^-1).
  eqp_issig_contr issig_magma; cbn; intros [X m].
  - exists equiv_idmap.  intros x0 x1.  reflexivity.
  - contr_sigsig X (equiv_idmap X).
    exact (@contr_equiv' _ _
           (equiv_functor_sigma_id (fun f => equiv_path_forall2 _ _))^-1
           (contr_basedpaths _)).
Defined.

(* This also follows directly from Magma Univalence. *)
Definition equiv_magmamap `{Funext} {X Y : Magma} (Z : Magma)
  (e : MagmaEquiv X Y) : MagmaMap Y Z <~> MagmaMap X Z.
Proof.
  serapply equiv_adjointify.
  + exact (fun f => magmamap_compose f e).
  + exact (fun g => magmamap_compose g (magmaequiv_inverse e)).
  + unfold Sect; intro f.
    refine (_ @ _).
    1:apply magmamap_compose_assoc.
    refine ((ap (magmamap_compose f) (ap magmamap (mecompose_Ve e))) @ _).
    apply magmamap_compose_f1.
  + unfold Sect; intro g.
    refine (_ @ _).
    1:apply magmamap_compose_assoc.
    refine ((ap (magmamap_compose g) (ap magmamap (mecompose_eV e))) @ _).
    apply magmamap_compose_f1.
Defined.

Definition magma_loops (X : pType) : Magma
  := Build_Magma (loops X) concat.

(** This is for n.+1 since at n=0 no magma to be found. *)
Definition iterated_magma_loops (n : nat) (X : pType) : Magma
  := Build_Magma (iterated_loops (S n) X) concat.

Local Open Scope pointed_scope.

Definition magma_loops_functor {X Y : pType}
  : (X ->* Y) -> MagmaMap (magma_loops X) (magma_loops Y).
Proof.
  intro f.
  simple notypeclasses refine (Build_MagmaMap _ _ _ _).
  + exact (loops_functor f).
  + exact (loops_functor_pp f).
Defined.

Definition magma_loops_functor_compose {X Y Z : pType} (f : Y ->* Z) (g : X ->* Y)
  : magma_loops_functor (f o* g)
    == magmamap_compose (magma_loops_functor f) (magma_loops_functor g).
Proof.
  apply loops_functor_compose.
Defined.

Definition iterated_magma_loops_functor {X Y : pType} (n : nat)
  : (X ->* Y) -> MagmaMap (iterated_magma_loops n X) (iterated_magma_loops n Y).
Proof.
  intro f.
  simple notypeclasses refine (Build_MagmaMap _ _ _ _).
  + exact (iterated_loops_functor n.+1 f).
  + exact (iterated_loops_functor_pp f n).
Defined.

Definition iterated_magma_loops_functor_compose {X Y Z : pType} (n : nat)
  (f : Y ->* Z) (g : X ->* Y) : iterated_magma_loops_functor n (f o* g)
  == magmamap_compose (iterated_magma_loops_functor n f)
      (iterated_magma_loops_functor n g).
Proof.
  apply iterated_loops_functor_compose.
Defined.

Global Instance isequiv_magma_loops_functor {X Y : pType} (f : X ->* Y)
  : IsEquiv f -> IsEquiv (magma_loops_functor f).
Proof.
  intro e.
  set (g := Build_pEquiv _ _ f e).
  unfold magma_loops_functor.
  unfold magmamap_map.
  exact (pointed_isequiv _ _ (pequiv_loops_functor g)).
Defined.

Global Instance isequiv_iterated_magma_loops_functor {X Y : pType} {n : nat}
  {f : X ->* Y} : IsEquiv f -> IsEquiv (iterated_magma_loops_functor n f).
Proof.
  revert X Y f.
  induction n; exact _.
Defined.

Definition group_to_magma : Group -> Magma
  := fun G => Build_Magma G _.

Coercion group_to_magma : Group >-> Magma.

Definition equiv_grp_homo_magma_map `{F : Funext} (G H : Group)
  : GroupHomomorphism G H <~> MagmaMap G H.
(* The proof is more complicated than expected because a GroupHomomorphism
   is required to preserve the identity, even though this is automatic. *)
Proof.
  serapply equiv_adjointify.
  + intro f.
    serapply (Build_MagmaMap G H f).
  + intro f.
    serapply (Build_GroupHomomorphism f).
    apply (magmamap_op_preserving G H f).
  + cbn; reflexivity.
  + intro f.
    destruct f as [f p].
    unfold Build_GroupHomomorphism.
    cbn.  apply ap.
    serapply path_ishprop.
Defined.

(** n-connected cover *)
Definition cover (n : trunc_index) (X : pType) : pType
  := @pfiber X (pTr n X) ptr.

Global Instance isconnected_cover (n : trunc_index) (X : pType)
  : IsConnected n (cover n X) := _.

(* The projection map from the n-connected cover to the type. *)
Definition cover_proj (n : trunc_index) {X : pType} : cover n X ->* X.
Proof.
  serapply Build_pMap.
  + apply pr1.
  + reflexivity.
Defined.

Global Instance mapinO_cover_proj (n : trunc_index) {X : pType}
  : IsTruncMap n (@cover_proj n X).
Proof.
  serapply mapinO_pr1.
Defined.

(* Lemma 2.3 *)
Global Instance isequiv_postcompose_cover_proj
  (n : trunc_index) (X : pType) (Z : pType) `{IsConnected n Z}
  : IsEquiv (fun f : Z ->* _ => @cover_proj n X o* f).
Proof.
Admitted.

Definition lemma_2_3 (n : nat) (X : pType) (Z : pType) `{IsConnected n Z}
  : (Z ->* cover n X) <~> (Z ->* X)
  := Build_Equiv _ _ _ (isequiv_postcompose_cover_proj n X Z).

(* Truncated magma *)
Definition mTr (n : trunc_index) (X : Magma) : Magma.
Proof.
  serapply (Build_Magma (Tr n X)).
  intros x y.
  strip_truncations.
  exact (tr (sg_op x y)).
Defined.

Definition issemigrouppreserving_tr (X : Magma) n
  : @IsSemiGroupPreserving X (mTr n X) _ _ tr.
Proof.
  intros x y.
  reflexivity.
Defined.

Global Instance isequiv_magmamap_precompose_hset `{Funext} {A B C : Magma}
  (f : MagmaMap A B) `{IsHSet C}
  : IsEquiv f -> IsEquiv (fun g : MagmaMap B C => magmamap_compose g f).
Proof.
  intro e.
  serapply isequiv_adjointify.
  { intro g.
    refine (magmamap_compose g _).
    serapply (Build_MagmaMap _ _ f^-1). }
  { intro g.
    serapply path_magmamap_hset.
    intro; apply (ap g).
    apply eissect. }
  intro g.
  serapply path_magmamap_hset.
  intro; apply (ap g).
  apply eisretr.
Defined.

Global Instance isequiv_magmamap_postcompose_hset `{Funext} {A B C : Magma}
  (f : MagmaMap B C) `{IsHSet C} `{IsHSet B}
  : IsEquiv f -> IsEquiv (fun g : MagmaMap A B => magmamap_compose f g).
Proof.
  intro e.
  serapply isequiv_adjointify.
  { intro g.
    refine (magmamap_compose _ g).
    serapply (Build_MagmaMap _ _ f^-1). }
  { intro g.
    serapply path_magmamap_hset.
    intro x.
    apply eisretr. }
  intro g.
  serapply path_magmamap_hset.
  intro; cbn; apply eissect.
Defined.

(** BVR 5.1 *)
Lemma theorem_2_1 (n : nat) (X Y : pType) `{IsConnected n X} `{IsConnected n Y}
  `{IsTrunc n.+1 X} `{IsTrunc n.+1 Y}
  : IsEquiv (@iterated_magma_loops_functor X Y n).
Proof.
Admitted.

(* This should be in Loops.v. *)
Global Instance ishset_iterated_magma_loops `{Univalence} (n : nat)
  {X : pType} `{IsTrunc n.+1 X}
  : IsHSet (iterated_magma_loops n X).
Proof.
  unfold iterated_magma_loops.
  unfold magma_type.
  revert X H0.
  induction n.
  - intros X H0.
    apply istrunc_loops.
    exact H0.
  - intros X H0.
    apply (trunc_equiv _ (unfold_iterated_loops' _ _)^-1).
    (* The induction hypothesis and H0 get used automatically by Coq. *)
Defined.

Definition pfiber_loops_functor {A B : pType} (f : A ->* B)
  : loops (pfiber f) <~>* pfiber (loops_functor f).
Proof.
  serapply Build_pEquiv'.
  { symmetry.
    etransitivity.
    2: serapply equiv_path_sigma.
    simpl; unfold hfiber.
    serapply equiv_functor_sigma_id.
    intro p; cbn.
    rewrite transport_paths_Fl.
    refine (_ oE equiv_moveL_Mp _ _ _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    rewrite concat_p1.
    apply equiv_path_inverse. }
  by pointed_reduce.
Defined.

Definition pfiber_iterated_loops_functor {A B : pType} (n : nat) (f : A ->* B)
  : iterated_loops n (pfiber f) <~>* pfiber (iterated_loops_functor n f).
Proof.
  induction n.
  1: reflexivity.
  refine (pfiber_loops_functor _ o*E _).
  apply pequiv_loops_functor.
  apply IHn.
Defined.

Global Instance prop_2_5 `{Univalence} (n : nat)
  (X : pType) `{IsConnected n X}
  (Y : pType) `{IsTrunc n.+1 Y}
  : IsEquiv (@iterated_magma_loops_functor X Y n).
Proof.
  (** We prove this is an equivalence by constructing a commutative square of equivalenes *)
  serapply isequiv_commsq.
  (** Bottom left corner *)
  1: exact (pTr n.+1 X ->* Y).
  (** Bottom right corner *)
  1: exact (MagmaMap (iterated_magma_loops n (pTr n.+1 X))
    (iterated_magma_loops n Y)).
  (** Bottom horizontal map *)
  1: exact (iterated_magma_loops_functor n).
  (** Left vertical map *)
  { apply equiv_fun.
    apply equiv_ptr_rec. }
  (** Right vertical map *)
  { intro g.
    serapply (magmamap_compose g).
    apply iterated_magma_loops_functor.
    apply ptr. }
  (** The square commutes by functoriality of iterated_magma_loops *)
  { symmetry.
    intro f.
    apply path_magmamap_hset.
    apply iterated_magma_loops_functor_compose. }
  (** Immediately we have some equivalences. *)
  2: exact _.
  2: {
    Search IsEquiv.
  apply isequiv_magmamap_precompose_hset.
    1: exact _.
    apply isequiv_iterated_magma_loops_functor.
    (* TODO: but tr is not an equivalence? *)
    admit. }
  (** To prove this final map is an equivalence we use another commutative square. *)
  serapply isequiv_commsq.
  (** The bottom left type *)
  1: exact (pTr n.+1 X ->* cover n Y).
  (** The bottom right type *)
  1: exact (MagmaMap (iterated_magma_loops n (pTr n.+1 X))
    (iterated_magma_loops n (cover n Y))).
  (** The bottom map *)
  1: exact (iterated_magma_loops_functor n).
  (** The left map *)
  { apply equiv_fun.
    apply lemma_2_3.
    exact _. }
  (** The right map *)
  { intro g.
    serapply (fun x => magmamap_compose x g).
    apply iterated_magma_loops_functor.
    apply cover_proj. }
  (** The square commutes by functoriality of iterated_magma_loops *)
  { cbn.
    symmetry.
    intro f.
    apply path_magmamap_hset.
    apply iterated_magma_loops_functor_compose. }
  (** The left map is an equivalence *)
  2: exact _.
  2: { apply isequiv_magmamap_postcompose_hset.
    1,2: exact _.
    (** Argument by using UP of connected types and loop-space sphere stuff *)
    admit. }
  serapply theorem_2_1.
Admitted.

Definition magma_loops_pmap (Y Z : pType) : Magma.
Proof.
  serapply (Build_Magma (Y ->* Build_pType (magma_loops Z) idpath)).
  intros f g.
  serapply Build_pMap.
  { intro y.
    exact (sg_op (f y) (g y)). }
  simpl; by rewrite 2 point_eq.
Defined.

Definition pmap_const {X Y : pType} : X ->* Y
  := Build_pMap X Y (fun _ => point _) idpath.

Definition ispointed_pmap {X Y : pType} : IsPointed (X ->* Y)
  := pmap_const.

Notation "X ->** Y" := (Build_pType (X ->* Y) ispointed_pmap) (at level 15).

Definition ap_const' {A B : Type} {x y : A} (p : x = y) (f : A -> B) {b : B}
  (q : forall a, f a = b) : ap f p = q x @ (q y)^.
Proof.
  destruct p.
  symmetry.
  apply concat_pV.
Defined.

Definition foo `{Funext} {Y Z : pType}
  : MagmaMap (magma_loops (Y ->** Z)) (magma_loops_pmap Y Z).
Proof.
  simple notypeclasses refine (Build_MagmaMap _ _ _ _).
  + change (loops (Y ->** Z) -> magma_loops_pmap Y Z).
    change (loops (Y ->** Z) -> (Y ->* loops Z)).
    intro p.
    serapply Build_pMap.
    { intro y.
      exact (ap (fun f : Y ->* Z => pointed_fun f y) p). }
    serapply (ap_const' p _ point_eq).
  + intros p q.
    serapply path_pmap.
    serapply Build_pHomotopy.
    { intro x; cbn.
      exact (ap_pp _ p q). }
Admitted.



