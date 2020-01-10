Require Import Basics Types Pointed.
Require Import Algebra.Group.
Require Import EquivalenceVarieties.
Require Import Truncations.
Require Import PathAny.
Import TrM.

Record Magma := {
  magma_type :> Type;
  magma_op :> SgOp magma_type;
}.

Existing Instance magma_op.

Record MagmaMap (X Y : Magma) := {
  magmamap_map :> X -> Y;
  magmamap_op_preserving : IsSemiGroupPreserving magmamap_map;
}.

Existing Instance magmamap_op_preserving.

(** TODO make more global anyway *)
Existing Instance compose_sg_morphism.

Definition magmamap_compose {X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) : MagmaMap X Z
  := Build_MagmaMap _ _ (f o g) _.

Definition issig_MagmaMap {X Y : Magma}
  : _ <~> MagmaMap X Y := ltac:(issig).

Definition path_magmamap_hset `{Funext} {X Y : Magma} {f g : MagmaMap X Y}
  `{IsHSet Y}
  : f == g -> f = g.
Proof.
  intro p.
  apply (equiv_ap' issig_MagmaMap^-1 _ _)^-1.
  apply path_sigma_hprop.
  by apply path_forall.
Defined.

Record MagmaEquiv (X Y : Magma) := {
  magmamap :> MagmaMap X Y;
  magmamap_isequiv : IsEquiv (magmamap_map _ _ magmamap);
}.

Arguments magmamap {X Y} _.
Arguments magmamap_isequiv {X Y} _.

Definition magmaequiv_to_equiv {X Y : Magma} : MagmaEquiv X Y -> Equiv X Y
  := fun f => Build_Equiv _ _ f (magmamap_isequiv f).

Coercion magmaequiv_to_equiv : MagmaEquiv >-> Equiv.

Definition build_magmaequiv {X Y : Magma} (f : X -> Y) (e : IsEquiv f)
           (r : IsSemiGroupPreserving f) : MagmaEquiv X Y
  := (Build_MagmaEquiv X Y (Build_MagmaMap X Y f r) e).

Definition magma_idmap (X : Magma) : MagmaEquiv X X.
Proof.
  refine (build_magmaequiv idmap _ _).
  unfold IsSemiGroupPreserving.  reflexivity.
Defined.

Definition magmaequiv_inverse {X Y : Magma} (f : MagmaEquiv X Y) : MagmaEquiv Y X.
Proof.
  refine (build_magmaequiv (magmaequiv_to_equiv f)^-1 _ _).
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

Definition rearrange_sigmas (X : Magma)
  : { Yf : { Y : Type & X <~> Y } & { m : SgOp Yf.1 & IsSemiGroupPreserving Yf.2 }}
      <~> {Y : Magma & MagmaEquiv X Y }.
Proof.
  serapply equiv_adjointify.
  - intros [[Y [f e]] [m r]].
    set (Ym := Build_Magma Y m).
    exact (Ym; build_magmaequiv (Y:=Ym) f e r).
  - intros [[Y m] [[f r] e]].
    exact ((Y; Build_Equiv _ _ f e); (m; r)).
  - simpl. reflexivity.
  - simpl. reflexivity.
Defined.

(* This verifies that we have the right notion of equivalence of magmas. *)
Definition equiv_magmaequiv_path  `{Univalence} (X Y : Magma) : MagmaEquiv X Y <~> (X = Y).
Proof.
  apply equiv_path_from_contr.
  - intro; apply magma_idmap.
  - (* Goal: [forall x : Magma, Contr {y : Magma & MagmaEquiv x y}] *)
    intros [Z m].
    simple notypeclasses refine (contr_equiv' _ (rearrange_sigmas _)).
    (* Now we have { a : A & B a}, where both A and B are contractible sigma types.
       Get rid of A first. *)
    simpl.
    simple notypeclasses refine (contr_equiv' _ (equiv_contr_sigma _)^-1).
    + apply contr_basedequiv_fix.
    + (* Now we show that [B (center A)] is contractible. *)
      simpl.
      simple refine (contr_equiv' {m0 : SgOp Z & m = m0} _).
      simple refine (equiv_functor_sigma_id _).
      simpl.
      intro a.
      symmetry.
      apply equiv_path_forall2.
Defined.

Definition equiv_magmamap `{Funext} {X Y : Magma} (Z : Magma) `{IsHSet Z}
  (e : MagmaMap X Y) `{!IsEquiv e} : MagmaMap Y Z <~> MagmaMap X Z.
Proof.
  serapply equiv_adjointify.
  + intro f.
    exists (f o e).
    exact _.
  + intro g.
    exists (g o e^-1).
    exact _.
  + intro f.
    simpl.
    serapply path_magmamap_hset.
    intro x.
    apply (ap f).
    apply eissect.
  + intro g.
    simpl.
    serapply path_magmamap_hset.
    intro y.
    apply (ap g).
    apply eisretr.
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



