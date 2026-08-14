Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Types.Paths Colimits.Pushout.
Require Import Cubical.DPath Cubical.PathSquare Cubical.DPathCube
  Cubical.PathCube.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.
Require Import WildCat.Equiv WildCat.EquivGpd WildCat.Universe.
Require Import WildCat.Cylinder WildCat.Square WildCat.Yoneda WildCat.ZeroGroupoid
  WildCat.TwoFunctor WildCat.LimitsScratch.

Set Typeclasses Depth 4.

(** * Scratch work on pushouts in [Type] *)

Section TypeDiagonal.

  Context (J : Type) `{IsGraph J}.

Definition natmod_diagonal02_type_id
  (A : Type)
  : NatModification
      (F := diagonal02 Type J A)
      (G := diagonal02 Type J A)
      (fmap (diagonal02 Type J) (Id A))
      (nattrans_id (diagonal02 Type J A)).
Proof.
  snapply Build_NatModification.
  { exact (fun _ _ => 1). }
  intros i j f x.
  reflexivity.
Defined.

Definition natmod_diagonal02_type_comp
  {A B C : Type} (f : A -> B) (g : B -> C)
  : NatModification
      (F := diagonal02 Type J A)
      (G := diagonal02 Type J C)
      (fmap (diagonal02 Type J)
        (@cat_comp Type isgraph_type is01cat_type A B C g f))
      (nattrans_comp
        (F := diagonal02 Type J A)
        (G := diagonal02 Type J B)
        (K := diagonal02 Type J C)
        (fmap (diagonal02 Type J) g)
        (fmap (diagonal02 Type J) f)).
Proof.
  snapply Build_NatModification.
  { exact (fun _ _ => 1). }
  intros i j h x.
  reflexivity.
Defined.

Global Instance is1functor_diagonal02_type
  : Is1Functor (diagonal02 Type J).
Proof.
  snapply Build_Is1Functor.
  - intros A B f g p.
    exact (natmod_diagonal02 Type J p).
  - exact natmod_diagonal02_type_id.
  - intros A B C f g.
    exact (natmod_diagonal02_type_comp f g).
Defined.

Definition is1functor_fmap_diagonal02_type
  (A B : Type)
  : Is1Functor
      (@fmap Type (Fun02 J Type) _ _
        (diagonal02 Type J) _ A B).
Proof.
  snapply Build_Is1Functor.
  - intros f g p q h j x.
    exact (h x).
  - intros f j x.
    reflexivity.
  - intros f g h p q j x.
    reflexivity.
Defined.

Global Instance is2functor_diagonal02_type
  : Is2Functor (diagonal02 Type J).
Proof.
  snapply Build_Is2Functor.
  - exact is1functor_fmap_diagonal02_type.
  - intros A B C f f' g g' p q j x.
    cbn.
    exact (concat_p1 _ @ (concat_1p _)^).
  - intros A B C D f g h j x.
    reflexivity.
  - intros A B f j x.
    reflexivity.
  - intros A B f j x.
    reflexivity.
Defined.

Global Instance iscoherent_diagonal02_type
  : IsCoherentDiagonal02 Type J.
Proof.
  snapply Build_IsCoherentDiagonal02.
  - exact is1functor_diagonal02_type.
  - exact is2functor_diagonal02_type.
Defined.

End TypeDiagonal.


Section TypeDiagonalInterchange.

  Context (I J : Type) `{IsGraph I, IsGraph J}.

Definition nattrans_diagonal_interchange02_type_at
  (A : Type)
  : swapped_double_diagonal02 Type I J A
    $-> double_diagonal02 Type I J A.
Proof.
  snapply Build_NatTrans.
  { intro i.
    snapply Build_NatTrans.
    { exact (fun j x => x). }
    snapply Build_Is1Natural.
    intros j j' g x.
    reflexivity. }
  snapply Build_Is1Natural.
  intros i i' f.
  snapply Build_NatModification.
  { exact (fun j x => 1). }
  intros j j' g x.
  reflexivity.
Defined.

Definition nattrans_diagonal_interchange02_type
  : NatTrans
      (swapped_double_diagonal02 Type I J)
      (double_diagonal02 Type I J).
Proof.
  snapply Build_NatTrans.
  { exact nattrans_diagonal_interchange02_type_at. }
  snapply Build_Is1Natural.
  intros A B f.
  snapply Build_NatModification.
  { intro i.
    snapply Build_NatModification.
    { exact (fun j x => 1). }
    intros j j' g x.
    reflexivity. }
  intros i i' g.
  exact (cylinder_refl _).
Defined.

Definition natequiv_diagonal_interchange02_type
  : NatEquiv
      (swapped_double_diagonal02 Type I J)
      (double_diagonal02 Type I J)
  := Build_NatEquiv'
      nattrans_diagonal_interchange02_type.

Global Instance hasdiagonalinterchange02_type
  : HasDiagonalInterchange02 Type I J
  := Build_HasDiagonalInterchange02 Type I J
      natequiv_diagonal_interchange02_type.

End TypeDiagonalInterchange.

(*
About nattrans_diagonal_interchange02_type.

Definition nattrans_diagonal_interchange02_type_walking_span
  : NatTrans
      (swapped_double_diagonal02 Type WalkingSpan WalkingSpan)
      (double_diagonal02 Type WalkingSpan WalkingSpan)
  := nattrans_diagonal_interchange02_type WalkingSpan WalkingSpan.

About nattrans_diagonal_interchange02_type_walking_span.
*)

(** ** Pushouts in [Type] *)

(** The recursion data for a pushout, equipped below with the 0-groupoid structure that retains the square coherence between homotopies. *)
Record PushoutRecData {A B C P : Type} (f : A -> B) (g : A -> C) := {
  pushout_rec_left : B -> P;
  pushout_rec_right : C -> P;
  pushout_rec_glue
    : pushout_rec_left o f == pushout_rec_right o g;
}.

Arguments PushoutRecData {A B C P} f g.
Arguments Build_PushoutRecData {A B C P f g}
  pushout_rec_left pushout_rec_right pushout_rec_glue.
Arguments pushout_rec_left {A B C P f g} r : rename.
Arguments pushout_rec_right {A B C P f g} r : rename.
Arguments pushout_rec_glue {A B C P f g} r a : rename.

Definition pushout_rec {A B C P : Type} {f : A -> B} {g : A -> C}
  (r : PushoutRecData (P := P) f g) : Pushout f g -> P
  := Pushout_rec P (pushout_rec_left r) (pushout_rec_right r)
       (pushout_rec_glue r).

Definition pushout_rec_beta_glue {A B C P : Type}
  {f : A -> B} {g : A -> C}
  (r : PushoutRecData (P := P) f g) (a : A)
  : ap (pushout_rec r) (pglue a) = pushout_rec_glue r a
  := Pushout_rec_beta_pglue P _ _ _ a.

Definition pushoutrecdata_fun {A B C P Q : Type}
  {f : A -> B} {g : A -> C} (k : P -> Q)
  (r : PushoutRecData (P := P) f g)
  : PushoutRecData (P := Q) f g.
Proof.
  snapply Build_PushoutRecData.
  - exact (k o pushout_rec_left r).
  - exact (k o pushout_rec_right r).
  - exact (fun a => ap k (pushout_rec_glue r a)).
Defined.

Definition pushoutrecdata_pushout {A B C : Type}
  (f : A -> B) (g : A -> C)
  : PushoutRecData (P := Pushout f g) f g
  := Build_PushoutRecData pushl pushr pglue.

Definition pushout_rec_inv {A B C P : Type}
  {f : A -> B} {g : A -> C} (k : Pushout f g -> P)
  : PushoutRecData (P := P) f g
  := pushoutrecdata_fun k (pushoutrecdata_pushout f g).

Record PushoutRecPath {A B C P : Type} {f : A -> B} {g : A -> C}
  (r s : PushoutRecData (P := P) f g) := {
  pushout_rec_path_left
    : pushout_rec_left r == pushout_rec_left s;
  pushout_rec_path_right
    : pushout_rec_right r == pushout_rec_right s;
  pushout_rec_path_glue : forall a,
    pushout_rec_glue r a @ pushout_rec_path_right (g a)
      = pushout_rec_path_left (f a) @ pushout_rec_glue s a;
}.

Arguments PushoutRecPath {A B C P f g} r s.
Arguments pushout_rec_path_left {A B C P f g r s} p b : rename.
Arguments pushout_rec_path_right {A B C P f g r s} p c : rename.
Arguments pushout_rec_path_glue {A B C P f g r s} p a : rename.

Definition bundle_pushoutrecpath {A B C P : Type}
  {f : A -> B} {g : A -> C}
  {l : B -> P} {r : C -> P} {p q : l o f == r o g}
  (h : p == q)
  : PushoutRecPath
      (Build_PushoutRecData l r p) (Build_PushoutRecData l r q).
Proof.
  snapply Build_PushoutRecPath.
  - reflexivity.
  - reflexivity.
  - intros a.
    napply equiv_p1_1q.
    apply h.
Defined.

Ltac bundle_pushoutrecpath :=
  hnf;
  match goal with |- PushoutRecPath ?R ?S =>
    rapply (bundle_pushoutrecpath
      (p := pushout_rec_glue R) (q := pushout_rec_glue S) _)
  end.

Definition pushout_rec_beta {A B C P : Type}
  {f : A -> B} {g : A -> C} (r : PushoutRecData (P := P) f g)
  : PushoutRecPath (pushout_rec_inv (pushout_rec r)) r.
Proof.
  unfold pushout_rec_inv, pushoutrecdata_fun, pushoutrecdata_pushout.
  apply bundle_pushoutrecpath.
  intro a.
  apply pushout_rec_beta_glue.
Defined.

Definition pushout_rec_path_ind {P : Type} (x y : P) (p : x = y)
  (Q : forall (x' y' : P) (p' : x' = y')
    (u : x = x') (v : y = y'),
    p @ v = u @ p' -> Type)
  (d : Q x y p idpath idpath (equiv_p1_1q idpath))
  : forall x' y' p' u v w, Q x' y' p' u v w.
Proof.
  intros x' y' p' u v w.
  destruct u, v.
  revert w.
  equiv_intro (equiv_p1_1q (p := p) (q := p')) w'.
  destruct w', p.
  exact d.
Defined.

Ltac pushout_recdata_interval_ind f g r a :=
  let rl := fresh in let rr := fresh in let rg := fresh in
  destruct r as [rl rr rg]; cbn;
  generalize (rg a); clear rg;
  generalize (rr (g a)); clear rr;
  generalize (rl (f a)); clear rl;
  intro rl;
  apply paths_ind.

Ltac pushout_rec_path_ind f g s h a :=
  let sl := fresh in let sr := fresh in let sg := fresh in
  destruct h as [sl sr sg]; cbn;
  generalize (sg a); clear sg;
  generalize (sr (g a)); clear sr;
  generalize (sl (f a)); clear sl;
  let sl := fresh in let sr := fresh in let sg := fresh in
  destruct s as [sl sr sg]; cbn;
  generalize (sg a); clear sg;
  generalize (sr (g a)); clear sr;
  generalize (sl (f a)); clear sl;
  apply pushout_rec_path_ind.

Global Instance isgraph_pushoutrecdata {A B C P : Type}
  (f : A -> B) (g : A -> C)
  : IsGraph (PushoutRecData (P := P) f g)
  := Build_IsGraph _ PushoutRecPath.

Global Instance is01cat_pushoutrecdata {A B C P : Type}
  (f : A -> B) (g : A -> C)
  : Is01Cat (PushoutRecData (P := P) f g).
Proof.
  snapply Build_Is01Cat.
  - intro r.
    bundle_pushoutrecpath.
    reflexivity.
  - intros r s t q p.
    snapply Build_PushoutRecPath.
    + exact (fun b => pushout_rec_path_left p b
        @ pushout_rec_path_left q b).
    + exact (fun c => pushout_rec_path_right p c
        @ pushout_rec_path_right q c).
    + intro a.
      pushout_rec_path_ind f g t q a.
      pushout_rec_path_ind f g s p a.
      pushout_recdata_interval_ind f g r a.
      reflexivity.
Defined.

Global Instance is0gpd_pushoutrecdata {A B C P : Type}
  (f : A -> B) (g : A -> C)
  : Is0Gpd (PushoutRecData (P := P) f g).
Proof.
  snapply Build_Is0Gpd.
  intros r s p.
  snapply Build_PushoutRecPath.
  - exact (fun b => (pushout_rec_path_left p b)^).
  - exact (fun c => (pushout_rec_path_right p c)^).
  - intro a.
    pushout_rec_path_ind f g s p a.
    pushout_recdata_interval_ind f g r a.
    reflexivity.
Defined.

Definition pushoutrecdata_0gpd {A B C : Type}
  (f : A -> B) (g : A -> C) (P : Type) : ZeroGpd
  := Build_ZeroGpd (PushoutRecData (P := P) f g) _ _ _.

Global Instance is0functor_pushoutrecdata_fun {A B C P Q : Type}
  {f : A -> B} {g : A -> C} (k : P -> Q)
  : Is0Functor (@pushoutrecdata_fun A B C P Q f g k).
Proof.
  snapply Build_Is0Functor.
  intros r s p.
  snapply Build_PushoutRecPath.
  - exact (fun b => ap k (pushout_rec_path_left p b)).
  - exact (fun c => ap k (pushout_rec_path_right p c)).
  - intro a.
    pushout_rec_path_ind f g s p a.
    pushout_recdata_interval_ind f g r a.
    reflexivity.
Defined.

Global Instance is0functor_pushoutrecdata_0gpd {A B C : Type}
  (f : A -> B) (g : A -> C)
  : Is0Functor (pushoutrecdata_0gpd f g).
Proof.
  snapply Build_Is0Functor.
  intros P Q k.
  exact (Build_Fun01 (pushoutrecdata_fun k)).
Defined.

Global Instance is1functor_pushoutrecdata_0gpd {A B C : Type}
  (f : A -> B) (g : A -> C)
  : Is1Functor (pushoutrecdata_0gpd f g).
Proof.
  snapply Build_Is1Functor.
  - intros P Q k l h r.
    snapply Build_PushoutRecPath.
    + exact (fun b => h (pushout_rec_left r b)).
    + exact (fun c => h (pushout_rec_right r c)).
    + intro a.
      destruct r as [rleft rright rglue]; cbn.
      destruct (rglue a); cbn.
      apply concat_1p_p1.
  - intros P r.
    bundle_pushoutrecpath.
    intro a.
    apply ap_idmap.
  - intros P Q R k l r.
    bundle_pushoutrecpath.
    intro a.
    apply (ap_compose k l).
Defined.

Definition pushoutrecdata_0gpd_fun {A B C : Type}
  (f : A -> B) (g : A -> C) : Fun11 Type ZeroGpd
  := Build_Fun11 _ _ (pushoutrecdata_0gpd f g).

Definition pushout_nattrans_recdata {A B C J : Type}
  {f : A -> B} {g : A -> C} (r : PushoutRecData (P := J) f g)
  : NatTrans (opyon_0gpd J) (pushoutrecdata_0gpd_fun f g).
Proof.
  snapply Build_NatTrans.
  - rapply opyoneda_0gpd.
    exact r.
  - exact _.
Defined.

Definition pushout_rec_inv_nattrans {A B C : Type}
  (f : A -> B) (g : A -> C)
  : NatTrans (opyon_0gpd (Pushout f g)) (pushoutrecdata_0gpd_fun f g)
  := pushout_nattrans_recdata (pushoutrecdata_pushout f g).

Definition pushout_rec_inv_natequiv {A B C : Type}
  (f : A -> B) (g : A -> C)
  : NatEquiv (opyon_0gpd (Pushout f g)) (pushoutrecdata_0gpd_fun f g).
Proof.
  snapply Build_NatEquiv'.
  - exact (pushout_rec_inv_nattrans f g).
  - intro P.
    napply isequiv_0gpd_issurjinj.
    snapply Build_IsSurjInj.
    + intro r.
      exists (pushout_rec r).
      apply pushout_rec_beta.
    + intros r s h.
      snapply Pushout_ind.
      * exact (pushout_rec_path_left h).
      * exact (pushout_rec_path_right h).
      * intro a.
        transport_paths FlFr.
        exact (pushout_rec_path_glue h a).
Defined.

Definition pushout_rec_natequiv {A B C : Type}
  (f : A -> B) (g : A -> C)
  := natequiv_inverse (pushout_rec_inv_natequiv f g).

(** ** The walking-span colimit *)

Definition span_pushout (X : Fun02 WalkingSpan Type) : Type
  := Pushout
    (fmap X (a := span_center) (b := span_left) tt)
    (fmap X (a := span_center) (b := span_right) tt).

Definition span_pushout_map
  {X Y : Fun02 WalkingSpan Type} (alpha : X $-> Y)
  : span_pushout X -> span_pushout Y
  := functor_pushout
    (alpha span_center) (alpha span_left) (alpha span_right)
    (isnat alpha (a := span_center) (a' := span_left) tt)
    (isnat alpha (a := span_center) (a' := span_right) tt).

Definition span_pushout_map_homotopy
  {X Y : Fun02 WalkingSpan Type}
  {alpha beta : X $-> Y} (p : alpha $== beta)
  : span_pushout_map alpha == span_pushout_map beta.
Proof.
  snapply functor_pushout_homotopic.
  - exact (natmod_component alpha beta p span_center).
  - exact (natmod_component alpha beta p span_left).
  - exact (natmod_component alpha beta p span_right).
  - intros x.
    exact (natmod_isnatural alpha beta p
      (a := span_center) (b := span_left) tt x).
  - intros x.
    exact (natmod_isnatural alpha beta p
      (a := span_center) (b := span_right) tt x).
Defined.


Global Instance is0functor_span_pushout
  : Is0Functor span_pushout.
Proof.
  snapply Build_Is0Functor.
  exact (fun X Y alpha => span_pushout_map alpha).
Defined.

Definition span_pushout_map_id
  (X : Fun02 WalkingSpan Type)
  : span_pushout_map (Id X) == idmap
  := functor_pushout_idmap.

Definition span_pushout_map_comp
  {X Y Z : Fun02 WalkingSpan Type}
  (alpha : X $-> Y) (beta : Y $-> Z)
  : span_pushout_map (beta $o alpha)
    == span_pushout_map beta o span_pushout_map alpha.
Proof.
  transitivity (functor_pushout
    (beta span_center o alpha span_center)
    (beta span_left o alpha span_left)
    (beta span_right o alpha span_right)
    (fun x => ap (beta span_left)
      (isnat alpha (a := span_center) (a' := span_left) tt x)
      @ isnat beta (a := span_center) (a' := span_left) tt
          (alpha span_center x))
    (fun x => ap (beta span_right)
      (isnat alpha (a := span_center) (a' := span_right) tt x)
      @ isnat beta (a := span_center) (a' := span_right) tt
          (alpha span_center x))).
  { snapply functor_pushout_homotopic.
    - exact (fun _ => 1).
    - exact (fun _ => 1).
    - exact (fun _ => 1).
    - intros x.
      unfold nattrans_comp, trans_comp.
      cbn.
      rewrite !concat_1p, !concat_p1.
      reflexivity.
    - intros x.
      unfold nattrans_comp, trans_comp.
      cbn.
      rewrite !concat_1p, !concat_p1.
      reflexivity. }
  exact (functor_pushout_compose
      (alpha span_center) (alpha span_left) (alpha span_right)
      (beta span_center) (beta span_left) (beta span_right)
      (isnat alpha (a := span_center) (a' := span_left) tt)
      (isnat alpha (a := span_center) (a' := span_right) tt)
      (isnat beta (a := span_center) (a' := span_left) tt)
      (isnat beta (a := span_center) (a' := span_right) tt)).
Defined.

Global Instance is1functor_span_pushout
  : Is1Functor span_pushout.
Proof.
  snapply Build_Is1Functor.
  - intros X Y alpha beta p.
    exact (span_pushout_map_homotopy p).
  - exact span_pushout_map_id.
  - intros X Y Z alpha beta.
    exact (span_pushout_map_comp alpha beta).
Defined.

Definition fun12_span_pushout
  : Fun12 (Fun02 WalkingSpan Type) Type
  := Build_Fun12 span_pushout.

Definition pointwise_span_pushout
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type))
  : Fun02 J Type.
Proof.
  snapply Build_Fun02.
  { exact (fun j => span_pushout (X j)). }
  snapply Build_Is0Functor.
  intros i j f.
  exact (span_pushout_map (fmap X f)).
Defined.


Definition iterated_span_pushout
  (X : Fun02 WalkingSpan (Fun02 WalkingSpan Type)) : Type
  := span_pushout (pointwise_span_pushout X).

Definition span_cocone_to_recdata
  (X : Fun02 WalkingSpan Type) (P : Type)
  (alpha : X $-> diagonal02 Type WalkingSpan P)
  : PushoutRecData (P := P)
      (fmap X (a := span_center) (b := span_left) tt)
      (fmap X (a := span_center) (b := span_right) tt).
Proof.
  snapply Build_PushoutRecData.
  { exact (alpha span_left). }
  { exact (alpha span_right). }
  intro x.
  exact (isnat alpha (a := span_center) (a' := span_left) tt x
    @ (isnat alpha (a := span_center) (a' := span_right) tt x)^).
Defined.

Definition span_recdata_to_cocone
  (X : Fun02 WalkingSpan Type) (P : Type)
  (r : PushoutRecData (P := P)
    (fmap X (a := span_center) (b := span_left) tt)
    (fmap X (a := span_center) (b := span_right) tt))
  : X $-> diagonal02 Type WalkingSpan P.
Proof.
  snapply Build_NatTrans.
  { intro i.
    destruct i.
    { exact (pushout_rec_left r). }
    { exact (pushout_rec_left r o
        fmap X (a := span_center) (b := span_left) tt). }
    exact (pushout_rec_right r). }
  snapply Build_Is1Natural.
  intros i j f.
  destruct i, j; destruct f; cbn beta.
  { reflexivity. }
  intro x.
  exact (pushout_rec_glue r x)^.
Defined.

Local Definition concat_inverse_square
  {A : Type} {l0 r0 c0 l1 r1 c1 : A}
  (s0 : l0 = c0) (t0 : r0 = c0)
  (s1 : l1 = c1) (t1 : r1 = c1)
  (pl : l0 = l1) (pr : r0 = r1) (pc : c0 = c1)
  (hl : s0 @ pc = pl @ s1)
  (hr : t0 @ pc = pr @ t1)
  : (s0 @ t0^) @ pr = pl @ (s1 @ t1^).
Proof.
  rewrite (moveL_pV t1 pr (t0 @ pc) hr^).
  rewrite !concat_pp_p.
  rewrite concat_V_pp.
  rewrite <- !concat_pp_p.
  rewrite hl.
  reflexivity.
Defined.

Definition span_cocone_to_recpath
  (X : Fun02 WalkingSpan Type) (P : Type)
  {alpha beta : X $-> diagonal02 Type WalkingSpan P}
  (p : alpha $== beta)
  : PushoutRecPath
      (span_cocone_to_recdata X P alpha)
      (span_cocone_to_recdata X P beta).
Proof.
  snapply Build_PushoutRecPath.
  { exact (natmod_component alpha beta p span_left). }
  { exact (natmod_component alpha beta p span_right). }
  intro x.
  napply (concat_inverse_square _ _ _ _ _ _
    (natmod_component alpha beta p span_center x)).
  { lhs' exact (whiskerL _ (ap_idmap _)^).
    exact (natmod_isnatural alpha beta p
      (a := span_center) (b := span_left) tt x). }
  lhs' exact (whiskerL _ (ap_idmap _)^).
  exact (natmod_isnatural alpha beta p
    (a := span_center) (b := span_right) tt x).
Defined.

Definition span_recpath_to_cocone
  (X : Fun02 WalkingSpan Type) (P : Type)
  {r s : PushoutRecData (P := P)
    (fmap X (a := span_center) (b := span_left) tt)
    (fmap X (a := span_center) (b := span_right) tt)}
  (p : PushoutRecPath r s)
  : span_recdata_to_cocone X P r
    $== span_recdata_to_cocone X P s.
Proof.
  snapply Build_NatModification.
  { intro i.
    destruct i.
    { exact (pushout_rec_path_left p). }
    { exact (fun x => pushout_rec_path_left p
        (fmap X (a := span_center) (b := span_left) tt x)). }
    exact (pushout_rec_path_right p). }
  intros i j f.
  destruct i, j; destruct f.
  { intro x.
    unfold span_recdata_to_cocone.
    unfold diagonal02.
    cbn.
    transitivity (pushout_rec_path_left p
      (fmap X (a := span_center) (b := span_left) tt x)).
    { exact (concat_1p _ @ ap_idmap _). }
    exact (concat_p1 _)^. }
  intro x.
  unfold span_recdata_to_cocone.
  unfold diagonal02.
  cbn.
  rewrite ap_idmap.
  napply moveR_Vp.
  transitivity ((pushout_rec_glue r x
    @ pushout_rec_path_right p _)
    @ (pushout_rec_glue s x)^).
  { napply moveL_pV.
    exact (pushout_rec_path_glue p x)^. }
  exact (concat_p_pp _ _ _)^.
Defined.

Definition span_recdata_issect
  (X : Fun02 WalkingSpan Type) (P : Type)
  (r : PushoutRecData (P := P)
    (fmap X (a := span_center) (b := span_left) tt)
    (fmap X (a := span_center) (b := span_right) tt))
  : PushoutRecPath
      (span_cocone_to_recdata X P
        (span_recdata_to_cocone X P r))
      r.
Proof.
  snapply Build_PushoutRecPath.
  { exact (fun _ => 1). }
  { exact (fun _ => 1). }
  intro x.
  unfold span_cocone_to_recdata.
  unfold span_recdata_to_cocone.
  cbn.
  exact (concat_p1 _ @ concat_1p _
    @ inv_V (pushout_rec_glue r x)
    @ (concat_1p _)^).
Defined.

Definition span_cocone_isretr
  (X : Fun02 WalkingSpan Type) (P : Type)
  (alpha : X $-> diagonal02 Type WalkingSpan P)
  : span_recdata_to_cocone X P
      (span_cocone_to_recdata X P alpha)
    $== alpha.
Proof.
  snapply Build_NatModification.
  { intro i.
    destruct i.
    { exact (fun _ => 1). }
    { exact (isnat alpha
        (a := span_center) (a' := span_left) tt). }
    exact (fun _ => 1). }
  intros i j f.
  destruct i, j; destruct f.
  { intro x.
    unfold span_recdata_to_cocone.
    unfold span_cocone_to_recdata.
    unfold diagonal02.
    cbn.
    exact (whiskerL 1 (ap_idmap _)). }
  intro x.
  unfold span_recdata_to_cocone.
  unfold span_cocone_to_recdata.
  unfold diagonal02.
  cbn.
  lhs' exact (whiskerR (inv_pV _ _) _).
  lhs' exact (whiskerL _ (ap_idmap _)).
  lhs' exact (concat_pV_p _ _).
  exact (concat_1p _)^.
Defined.

Definition fun01_span_cocone_to_recdata
  (X : Fun02 WalkingSpan Type) (P : Type)
  : cocone02 X P $->
      pushoutrecdata_0gpd
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt) P.
Proof.
  snapply Build_Fun01'.
  { exact (span_cocone_to_recdata X P). }
  intros alpha beta p.
  exact (span_cocone_to_recpath X P p).
Defined.

Definition fun01_span_recdata_to_cocone
  (X : Fun02 WalkingSpan Type) (P : Type)
  : @Hom ZeroGpd isgraph_0gpd
    (pushoutrecdata_0gpd
      (fmap X (a := span_center) (b := span_left) tt)
      (fmap X (a := span_center) (b := span_right) tt) P)
    (cocone02 X P).
Proof.
  snapply Build_Fun01'.
  { exact (span_recdata_to_cocone X P). }
  intros r s p.
  exact (span_recpath_to_cocone X P p).
Defined.

Definition equiv_span_cocone_recdata
  (X : Fun02 WalkingSpan Type) (P : Type)
  : cocone02 X P $<~>
      pushoutrecdata_0gpd
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt) P.
Proof.
  snapply cate_adjointify.
  - exact (fun01_span_cocone_to_recdata X P).
  - exact (fun01_span_recdata_to_cocone X P).
  - exact (span_recdata_issect X P).
  - exact (span_cocone_isretr X P).
Defined.

Definition nattrans_span_cocone_recdata
  (X : Fun02 WalkingSpan Type)
  : NatTrans (cocone02 X)
      (pushoutrecdata_0gpd_fun
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt)).
Proof.
  snapply Build_NatTrans.
  - exact (fun P => fun01_span_cocone_to_recdata X P).
  - snapply Build_Is1Natural.
    intros P Q k alpha.
    unfold fun01_span_cocone_to_recdata.
    unfold span_cocone_to_recdata.
    unfold cocone02, diagonal02.
    cbn beta.
    snapply Build_PushoutRecPath.
    { exact (fun _ => 1). }
    { exact (fun _ => 1). }
    intro x.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite ap_pp, ap_V.
    reflexivity.
Defined.

Global Instance catie_span_cocone_recdata
  (X : Fun02 WalkingSpan Type) (P : Type)
  : CatIsEquiv (fun01_span_cocone_to_recdata X P).
Proof.
  exact (catie_adjointify
    (fun01_span_cocone_to_recdata X P)
    (fun01_span_recdata_to_cocone X P)
    (span_recdata_issect X P)
    (span_cocone_isretr X P)).
Defined.

Definition natequiv_span_cocone_recdata
  (X : Fun02 WalkingSpan Type)
  : NatEquiv (cocone02 X)
      (pushoutrecdata_0gpd_fun
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt))
  := Build_NatEquiv' (nattrans_span_cocone_recdata X).

Definition span_pushout_iscolimit
  (X : Fun02 WalkingSpan Type)
  : IsColimit X (span_pushout X)
  := natequiv_compose
      (F := opyon_0gpd (span_pushout X))
      (G := pushoutrecdata_0gpd_fun
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt))
      (H := cocone02 X)
      (natequiv_inverse (natequiv_span_cocone_recdata X))
      (pushout_rec_inv_natequiv
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt)).


(*
Definition span_pushout_unit_component
  (X : Fun02 WalkingSpan Type)
  : X $-> diagonal02 Type WalkingSpan (span_pushout X)
  := span_recdata_to_cocone X (span_pushout X)
      (pushoutrecdata_pushout
        (fmap X (a := span_center) (b := span_left) tt)
        (fmap X (a := span_center) (b := span_right) tt)).

Definition span_pushout_counit_component (P : Type)
  : span_pushout (diagonal02 Type WalkingSpan P) -> P.
Proof.
  snapply Pushout_rec.
  - exact idmap.
  - exact idmap.
  - exact (fun _ => 1).
Defined.

Definition nattrans_span_pushout_counit
  : NatTrans
      (span_pushout o diagonal02 Type WalkingSpan)
      idmap.
Proof.
  snapply Build_NatTrans.
  { exact span_pushout_counit_component. }
  snapply Build_Is1Natural.
  intros P Q f.
  snapply Pushout_ind.
  - reflexivity.
  - reflexivity.
  - intros x.
    transport_paths FlFr.
    rewrite !concat_1p, !concat_p1.
    lhs exact (ap_compose
      (fmap (span_pushout o diagonal02 Type WalkingSpan) f)
      (span_pushout_counit_component Q) (pglue x)).
    rhs exact (ap_compose (span_pushout_counit_component P)
      (fmap idmap f) (pglue x)).
    rewrite functor_pushout_beta_pglue.
    rewrite Pushout_rec_beta_pglue.
    unfold diagonal02.
    cbn.
    rewrite concat_1p, concat_p1.
    unfold span_pushout_counit_component.
    napply Pushout_rec_beta_pglue.
Defined.

Definition natmod_span_pushout_unit_naturality
  {X Y : Fun02 WalkingSpan Type} (alpha : X $-> Y)
  : NatModification
      (@cat_comp (Fun02 WalkingSpan Type) _
        (is01cat_fun02 WalkingSpan Type)
        X Y (diagonal02 Type WalkingSpan (span_pushout Y))
        (span_pushout_unit_component Y) alpha)
      (@cat_comp (Fun02 WalkingSpan Type) _
        (is01cat_fun02 WalkingSpan Type)
        X (diagonal02 Type WalkingSpan (span_pushout X))
        (diagonal02 Type WalkingSpan (span_pushout Y))
        (fmap (diagonal02 Type WalkingSpan)
          (span_pushout_map alpha))
        (span_pushout_unit_component X)).
Proof.
  snapply Build_NatModification.
  { intro i.
    destruct i.
    - exact (fun _ => 1).
    - exact (fun x =>
        (ap pushl (isnat alpha
          (a := span_center) (a' := span_left) tt x))^).
    - exact (fun _ => 1). }
  intros i j f.
  destruct i, j; destruct f; cbn beta.
  - intros x.
    unfold Cylinder, Square.
    cbn.
    rewrite !concat_1p, !concat_p1, ap_idmap, concat_pV.
    reflexivity.
  - intros x.
    unfold Cylinder, Square.
    cbn.
    rewrite !concat_1p, !concat_p1, ap_idmap.
    rewrite ap_V.
    rewrite functor_pushout_beta_pglue.
    rewrite !inv_pp.
    rhs' exact (whiskerR
      ((ap (fun p => p^) (inverse_ap pushr
          (isnat alpha (a := span_center)
            (a' := span_right) tt x)))^
        @ inv_V (ap pushr
          (isnat alpha (a := span_center)
            (a' := span_right) tt x))) _).
    exact (concat_pp_p _ _ _).
Defined.

Definition nattrans_span_pushout_unit
  : NatTrans idmap
      (diagonal02 Type WalkingSpan o span_pushout).
Proof.
  snapply Build_NatTrans.
  { exact span_pushout_unit_component. }
  snapply Build_Is1Natural.
  intros X Y alpha.
  exact (natmod_span_pushout_unit_naturality alpha).
Defined.

Definition natmod_span_pushout_mate_naturality_left_associator
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (nattrans_comp
        (F := X) (G := Y)
        (K := diagonal02 Type WalkingSpan (span_pushout Y))
        (span_pushout_unit_component Y) u))
  := natmod_assoc_from_cylinder u
      (span_pushout_unit_component Y)
      (fmap (diagonal02 Type WalkingSpan) b).

Definition natmod_span_pushout_mate_naturality_left_unit_whisker
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (nattrans_comp
        (F := X) (G := Y)
        (K := diagonal02 Type WalkingSpan (span_pushout Y))
        (span_pushout_unit_component Y) u))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan (span_pushout Y))
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u))
        (span_pushout_unit_component X)))
  := natmod_postcompose
      (A := WalkingSpan) (B := Type)
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (natmod_span_pushout_unit_naturality u).

Definition natmod_span_pushout_mate_naturality_left_unit_raw
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan (span_pushout Y))
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u))
        (span_pushout_unit_component X))).
Proof.
  exact (natmod_comp
    (natmod_span_pushout_mate_naturality_left_unit_whisker u b)
    (natmod_span_pushout_mate_naturality_left_associator u b)).
Defined.

Definition natmod_span_pushout_mate_naturality_left_unit
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan (span_pushout Y))
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u))
        (span_pushout_unit_component X))).
Proof.
  snapply Build_NatModification.
  { exact (fun w x => ap b
      (natmod_component _ _
        (natmod_span_pushout_unit_naturality u) w x)). }
  intros i j f.
  rapply cylinder_rewrite_left.
  { exact (cat_idr _)^$. }
  rapply cylinder_rewrite_right.
  { exact (cat_idr _)^$. }
  exact (natmod_isnatural _ _
    (natmod_span_pushout_mate_naturality_left_unit_raw u b) f).
Defined.

Definition natmod_span_pushout_mate_naturality_left_reassociator
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout Y))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) b)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan (span_pushout Y))
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u))
        (span_pushout_unit_component X)))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u)))
      (span_pushout_unit_component X))
  := natmod_inverse
      (A := WalkingSpan) (B := Type)
      (natmod_assoc_from_cylinder
        (span_pushout_unit_component X)
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u))
        (fmap (diagonal02 Type WalkingSpan) b)).

Definition natmod_span_pushout_mate_naturality_left_assoc_raw
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u)))
      (span_pushout_unit_component X)).
Proof.
  exact (natmod_comp
    (natmod_span_pushout_mate_naturality_left_reassociator u b)
    (natmod_span_pushout_mate_naturality_left_unit u b)).
Defined.

Definition natmod_span_pushout_mate_naturality_left_assoc
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u)))
      (span_pushout_unit_component X)).
Proof.
  snapply Build_NatModification.
  { exact (fun w x => ap b
      (natmod_component _ _
        (natmod_span_pushout_unit_naturality u) w x)). }
  intros i j f.
  rapply cylinder_rewrite_left.
  { exact (cat_idl _)^$. }
  rapply cylinder_rewrite_right.
  { exact (cat_idl _)^$. }
  exact (natmod_isnatural _ _
    (natmod_span_pushout_mate_naturality_left_assoc_raw u b) f).
Defined.

Definition natmod_span_pushout_mate_naturality_left_compositor
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (fmap (diagonal02 Type WalkingSpan) (span_pushout_map u)))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X))
  := natmod_precompose
      (A := WalkingSpan) (B := Type)
      (K := X)
      (F := diagonal02 Type WalkingSpan (span_pushout X))
      (G := diagonal02 Type WalkingSpan Q)
      (span_pushout_unit_component X)
      (natmod_inverse (natmod_diagonal02_type_comp WalkingSpan
        (span_pushout_map u) b)).

Definition natmod_span_pushout_mate_naturality_left_raw
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X)).
Proof.
  exact (natmod_comp
    (natmod_span_pushout_mate_naturality_left_compositor u b)
    (natmod_span_pushout_mate_naturality_left_assoc u b)).
Defined.

Definition natmod_span_pushout_mate_naturality_left
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X)).
Proof.
  snapply Build_NatModification.
  { exact (fun w x => ap b
      (natmod_component _ _
        (natmod_span_pushout_unit_naturality u) w x)). }
  intros i j f.
  rapply cylinder_rewrite_left.
  { exact (cat_idl _)^$. }
  rapply cylinder_rewrite_right.
  { exact (cat_idl _)^$. }
  exact (natmod_isnatural _ _
    (natmod_span_pushout_mate_naturality_left_raw u b) f).
Defined.

Definition natmod_span_pushout_mate_naturality_right_square
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) (k o a))
      (span_pushout_unit_component X))
  := natmod_precompose
      (A := WalkingSpan) (B := Type)
      (K := X)
      (F := diagonal02 Type WalkingSpan (span_pushout X))
      (G := diagonal02 Type WalkingSpan Q)
      (span_pushout_unit_component X)
      (natmod_diagonal02 Type WalkingSpan h).

Definition natmod_span_pushout_mate_naturality_right_compositor
  {X : Fun02 WalkingSpan Type}
  {P Q : Type} (a : span_pushout X -> P) (k : P -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) (k o a))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan P)
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) k)
        (fmap (diagonal02 Type WalkingSpan) a))
      (span_pushout_unit_component X))
  := natmod_precompose
      (A := WalkingSpan) (B := Type)
      (K := X)
      (F := diagonal02 Type WalkingSpan (span_pushout X))
      (G := diagonal02 Type WalkingSpan Q)
      (span_pushout_unit_component X)
      (natmod_diagonal02_type_comp WalkingSpan a k).

Definition natmod_span_pushout_mate_naturality_right_assoc
  {X : Fun02 WalkingSpan Type}
  {P Q : Type} (a : span_pushout X -> P) (k : P -> Q)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan P)
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) k)
        (fmap (diagonal02 Type WalkingSpan) a))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan P)
        (fmap (diagonal02 Type WalkingSpan) a)
        (span_pushout_unit_component X)))
  := natmod_assoc_from_cylinder
      (span_pushout_unit_component X)
      (fmap (diagonal02 Type WalkingSpan) a)
      (fmap (diagonal02 Type WalkingSpan) k).

Definition natmod_span_pushout_mate_naturality_right_comp_raw
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan P)
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) k)
        (fmap (diagonal02 Type WalkingSpan) a))
      (span_pushout_unit_component X)).
Proof.
  exact (natmod_comp
    (natmod_span_pushout_mate_naturality_right_compositor a k)
    (natmod_span_pushout_mate_naturality_right_square u a b k h)).
Defined.

Definition natmod_span_pushout_mate_naturality_right_comp
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan (span_pushout X))
        (G := diagonal02 Type WalkingSpan P)
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) k)
        (fmap (diagonal02 Type WalkingSpan) a))
      (span_pushout_unit_component X)).
Proof.
  snapply Build_NatModification.
  { exact (fun w x => h (span_pushout_unit_component X w x)). }
  intros i j f.
  rapply cylinder_rewrite_left.
  { exact (cat_idl _)^$. }
  rapply cylinder_rewrite_right.
  { exact (cat_idl _)^$. }
  exact (natmod_isnatural _ _
    (natmod_span_pushout_mate_naturality_right_comp_raw
      u a b k h) f).
Defined.

Definition natmod_span_pushout_mate_naturality_right_raw
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan P)
        (fmap (diagonal02 Type WalkingSpan) a)
        (span_pushout_unit_component X))).
Proof.
  exact (natmod_comp
    (natmod_span_pushout_mate_naturality_right_assoc a k)
    (natmod_span_pushout_mate_naturality_right_comp u a b k h)).
Defined.

Definition natmod_span_pushout_mate_naturality_right
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X)
      (G := diagonal02 Type WalkingSpan (span_pushout X))
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan)
        (b o span_pushout_map u))
      (span_pushout_unit_component X))
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan P)
        (fmap (diagonal02 Type WalkingSpan) a)
        (span_pushout_unit_component X))).
Proof.
  snapply Build_NatModification.
  { exact (fun w x => h (span_pushout_unit_component X w x)). }
  intros i j f.
  rapply cylinder_rewrite_left.
  { exact (cat_idl _)^$. }
  rapply cylinder_rewrite_right.
  { exact (cat_idl _)^$. }
  exact (natmod_isnatural _ _
    (natmod_span_pushout_mate_naturality_right_raw u a b k h) f).
Defined.

Definition natmod_span_pushout_mate_naturality
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y) (K := diagonal02 Type WalkingSpan Q)
      (nattrans_comp
        (F := Y)
        (G := diagonal02 Type WalkingSpan (span_pushout Y))
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) b)
        (span_pushout_unit_component Y)) u)
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k)
      (nattrans_comp
        (F := X)
        (G := diagonal02 Type WalkingSpan (span_pushout X))
        (K := diagonal02 Type WalkingSpan P)
        (fmap (diagonal02 Type WalkingSpan) a)
        (span_pushout_unit_component X))).
Proof.
  exact (natmod_comp
    (natmod_span_pushout_mate_naturality_right u a b k h)
    (natmod_span_pushout_mate_naturality_left u b)).
Defined.

Definition natmod_span_pushout_mate_naturality_left_component
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {Q : Type} (b : span_pushout Y -> Q) (w : WalkingSpan)
  : natmod_component _ _
      (natmod_span_pushout_mate_naturality_left u b) w
    $== cat_postwhisker (A := Type) b
      (natmod_component _ _
        (natmod_span_pushout_unit_naturality u) w)
  := fun _ => 1.

Definition natmod_span_pushout_mate_naturality_right_component
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  (w : WalkingSpan)
  : natmod_component _ _
      (natmod_span_pushout_mate_naturality_right u a b k h) w
    $== cat_prewhisker (A := Type) h
      (span_pushout_unit_component X w)
  := fun _ => 1.

Definition natmod_span_pushout_mate_naturality_component
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : span_pushout X -> P) (b : span_pushout Y -> Q)
  (k : P -> Q)
  (h : Square (A := Type) a b (span_pushout_map u) k)
  (w : WalkingSpan)
  : natmod_component _ _
      (natmod_span_pushout_mate_naturality u a b k h) w
    $== natmod_component _ _
      (natmod_span_pushout_unit_naturality u) w $@v h.
Proof.
  unfold natmod_span_pushout_mate_naturality, natmod_comp.
  lhs' exact (cat_postwhisker
    (A := X w $-> Q)
    (natmod_component _ _
      (natmod_span_pushout_mate_naturality_right u a b k h) w)
    (natmod_span_pushout_mate_naturality_left_component u b w)).
  lhs' exact (cat_prewhisker
    (A := X w $-> Q)
    (natmod_span_pushout_mate_naturality_right_component
      u a b k h w)
    (cat_postwhisker (A := Type) b
      (natmod_component _ _
        (natmod_span_pushout_unit_naturality u) w))).
  intro x.
  change
    (ap b (natmod_component _ _
        (natmod_span_pushout_unit_naturality u) w x)
      @ h (span_pushout_unit_component X w x)
    = (1 @ ap b (natmod_component _ _
          (natmod_span_pushout_unit_naturality u) w x))
      @ ((1 @ h (span_pushout_unit_component X w x)) @ 1)).
  rewrite !concat_1p, !concat_p1.
  reflexivity.
Defined.

(** Taking the mate of every component turns a cocone over the pointwise pushout into a coherent two-variable cocone. *)
Definition nattrans_pointwise_span_pushout_mate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  (alpha : pointwise_span_pushout X
    $-> diagonal02 Type J P)
  : X $-> double_diagonal02 Type J WalkingSpan P.
Proof.
  snapply Build_NatTrans.
  { intro j.
    exact (nattrans_comp
      (A := WalkingSpan) (B := Type)
      (F := X j)
      (G := diagonal02 Type WalkingSpan (span_pushout (X j)))
      (K := diagonal02 Type WalkingSpan P)
      (fmap (diagonal02 Type WalkingSpan) (alpha j))
      (span_pushout_unit_component (X j))). }
  snapply Build_Is1Natural.
  intros i j f.
  exact (natmod_span_pushout_mate_naturality
    (fmap X f) (alpha i) (alpha j)
    (fmap (diagonal02 Type J P) f) (isnat alpha f)).
Defined.

Definition cylinder_span_pushout_mate_naturality
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  {a a' : span_pushout X -> P}
  {b b' : span_pushout Y -> Q} (k : P -> Q)
  {h : Square (A := Type) a b (span_pushout_map u) k}
  {h' : Square (A := Type) a' b' (span_pushout_map u) k}
  (p : a == a') (q : b == b')
  (c : Cylinder (A := Type)
    (f := span_pushout_map u) (g := k) p q h h')
  : Cylinder (A := Fun02 WalkingSpan Type)
      (f := u) (g := fmap (diagonal02 Type WalkingSpan) k)
      (natmod_precompose
        (span_pushout_unit_component X)
        (natmod_diagonal02 Type WalkingSpan p))
      (natmod_precompose
        (span_pushout_unit_component Y)
        (natmod_diagonal02 Type WalkingSpan q))
      (natmod_span_pushout_mate_naturality u a b k h)
      (natmod_span_pushout_mate_naturality u a' b' k h').
Proof.
  rapply Build_Cylinder_fun02.
  intro w.
  rapply cylinder_rewrite_front.
  { exact (natmod_span_pushout_mate_naturality_component
      u a b k h w). }
  rapply cylinder_rewrite_back.
  { exact (natmod_span_pushout_mate_naturality_component
      u a' b' k h' w). }
  exact (cylinder_vconcat_above
    (natmod_component _ _
      (natmod_span_pushout_unit_naturality u) w) c).
Defined.

Definition natmod_pointwise_span_pushout_mate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  {alpha beta : pointwise_span_pushout X
    $-> diagonal02 Type J P}
  (p : alpha $== beta)
  : nattrans_pointwise_span_pushout_mate X P alpha
    $== nattrans_pointwise_span_pushout_mate X P beta.
Proof.
  snapply Build_NatModification.
  { intro j.
    exact (natmod_precompose
      (span_pushout_unit_component (X j))
      (natmod_diagonal02 Type WalkingSpan
        (natmod_component alpha beta p j))). }
  intros i j f.
  exact (cylinder_span_pushout_mate_naturality
    (fmap X f) (fmap (diagonal02 Type J P) f)
    (natmod_component alpha beta p i)
    (natmod_component alpha beta p j)
    (natmod_isnatural alpha beta p f)).
Defined.

Definition fun01_pointwise_span_pushout_mate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  : opyon_0gpd (pointwise_span_pushout X)
      (diagonal02 Type J P)
    $-> opyon_0gpd X
      (double_diagonal02 Type J WalkingSpan P).
Proof.
  snapply Build_Fun01'.
  { exact (nattrans_pointwise_span_pushout_mate X P). }
  intros alpha beta p.
  exact (natmod_pointwise_span_pushout_mate X P p).
Defined.

Definition span_pushout_unmate_component
  (X : Fun02 WalkingSpan Type) (P : Type)
  (alpha : X $-> diagonal02 Type WalkingSpan P)
  : span_pushout X -> P
  := span_pushout_counit_component P o span_pushout_map alpha.

Definition span_pushout_unmate_naturality
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  (a : X $-> diagonal02 Type WalkingSpan P)
  (b : Y $-> diagonal02 Type WalkingSpan Q)
  (k : P -> Q)
  (h : NatModification
    (A := WalkingSpan) (B := Type)
    (F := X) (G := diagonal02 Type WalkingSpan Q)
    (nattrans_comp
      (F := X) (G := Y)
      (K := diagonal02 Type WalkingSpan Q) b u)
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k) a))
  : Square (A := Type)
      (span_pushout_unmate_component X P a)
      (span_pushout_unmate_component Y Q b)
      (span_pushout_map u) k.
Proof.
  unfold span_pushout_unmate_component.
  change (
    ((span_pushout_counit_component Q o span_pushout_map b)
      o span_pushout_map u)
    == k o
      (span_pushout_counit_component P o span_pushout_map a)).
  lhs' exact (cat_assoc (A := Type) (span_pushout_map u)
    (span_pushout_map b) (span_pushout_counit_component Q)).
  lhs' exact (cat_postwhisker (A := Type)
    (span_pushout_counit_component Q)
    (fun x => (span_pushout_map_comp u b x)^)).
  lhs' exact (cat_postwhisker (A := Type)
    (span_pushout_counit_component Q)
    (span_pushout_map_homotopy
      (X := X) (Y := diagonal02 Type WalkingSpan Q)
      (alpha := nattrans_comp
        (F := X) (G := Y)
        (K := diagonal02 Type WalkingSpan Q) b u)
      (beta := nattrans_comp
        (F := X) (G := diagonal02 Type WalkingSpan P)
        (K := diagonal02 Type WalkingSpan Q)
        (fmap (diagonal02 Type WalkingSpan) k) a) h)).
  lhs' exact (cat_postwhisker (A := Type)
    (span_pushout_counit_component Q)
    (span_pushout_map_comp a
      (fmap (diagonal02 Type WalkingSpan) k))).
  lhs' exact (cat_assoc_opp (A := Type) (span_pushout_map a)
    (span_pushout_map (fmap (diagonal02 Type WalkingSpan) k))
    (span_pushout_counit_component Q)).
  lhs' exact (cat_prewhisker (A := Type)
    (isnat nattrans_span_pushout_counit k)
    (span_pushout_map a)).
  exact (cat_assoc (A := Type) (span_pushout_map a)
    (span_pushout_counit_component P) k).
Defined.

Definition nattrans_pointwise_span_pushout_unmate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  (alpha : X $-> double_diagonal02 Type J WalkingSpan P)
  : pointwise_span_pushout X $-> diagonal02 Type J P.
Proof.
  snapply Build_NatTrans.
  { intro j.
    exact (span_pushout_unmate_component (X j) P (alpha j)). }
  snapply Build_Is1Natural.
  intros i j f.
  exact (span_pushout_unmate_naturality
    (fmap X f) (alpha i) (alpha j)
    (fmap (diagonal02 Type J P) f) (isnat alpha f)).
Defined.

Definition cylinder_span_pushout_unmate_naturality
  {X Y : Fun02 WalkingSpan Type} (u : X $-> Y)
  {P Q : Type}
  {a a' : X $-> diagonal02 Type WalkingSpan P}
  {b b' : Y $-> diagonal02 Type WalkingSpan Q}
  (k : P -> Q)
  {h : NatModification
    (nattrans_comp
      (F := X) (G := Y)
      (K := diagonal02 Type WalkingSpan Q) b u)
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k) a)}
  {h' : NatModification
    (nattrans_comp
      (F := X) (G := Y)
      (K := diagonal02 Type WalkingSpan Q) b' u)
    (nattrans_comp
      (F := X) (G := diagonal02 Type WalkingSpan P)
      (K := diagonal02 Type WalkingSpan Q)
      (fmap (diagonal02 Type WalkingSpan) k) a')}
  (p : a $== a') (q : b $== b')
  (c : Cylinder (A := Fun02 WalkingSpan Type)
    (f := u) (g := fmap (diagonal02 Type WalkingSpan) k)
    p q h h')
  : Cylinder (A := Type)
      (f := span_pushout_map u) (g := k)
      (cat_postwhisker (A := Type)
        (span_pushout_counit_component P)
        (span_pushout_map_homotopy p))
      (cat_postwhisker (A := Type)
        (span_pushout_counit_component Q)
        (span_pushout_map_homotopy q))
      (span_pushout_unmate_naturality u a b k h)
      (span_pushout_unmate_naturality u a' b' k h').
Proof.
  unfold Cylinder.
  (** On the point constructors this is the supplied inner cylinder.  The glue equation computes from the coherence already built into [span_pushout_map_homotopy]. *)
  snapply Pushout_ind.
  - intro x.
    unfold span_pushout_unmate_naturality.
    unfold Square.
    unfold cat_assoc, cat_assoc_opp.
    unfold cat_postwhisker, cat_prewhisker.
    unfold is1cat_is1cat_strong, is1cat_strong_type.
    unfold is0functor_type_postcomp, is0functor_type_precomp.
    unfold cat_assoc_strong, cat_assoc_opp_strong.
    unfold GpdHom_path, Hom_path.
    unfold fmap, cat_postcomp, cat_precomp.
    unfold span_pushout_map_comp.
    cbn beta.
    unfold span_pushout_map_homotopy.
    exact (c span_left x).
  - intro x.
    unfold span_pushout_unmate_naturality.
    unfold span_pushout_map_homotopy.
    unfold Square.
    unfold cat_assoc, cat_assoc_opp.
    unfold cat_postwhisker, cat_prewhisker.
    unfold is1cat_is1cat_strong, is1cat_strong_type.
    unfold is0functor_type_postcomp, is0functor_type_precomp.
    unfold cat_assoc_strong, cat_assoc_opp_strong.
    unfold GpdHom_path, Hom_path.
    unfold fmap, cat_postcomp, cat_precomp.
    unfold span_pushout_map_comp.
    cbn beta.
    exact (c span_right x).
  - intro x.
    reflexivity.
Defined.

Definition natmod_pointwise_span_pushout_unmate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  {alpha beta : X
    $-> double_diagonal02 Type J WalkingSpan P}
  (p : alpha $== beta)
  : nattrans_pointwise_span_pushout_unmate X P alpha
    $== nattrans_pointwise_span_pushout_unmate X P beta.
Proof.
  snapply Build_NatModification.
  { intro j.
    exact (span_pushout_counit_component P $@L
      span_pushout_map_homotopy
        (natmod_component alpha beta p j)). }
  intros i j f.
  exact (cylinder_span_pushout_unmate_naturality
    (fmap X f) (fmap (diagonal02 Type J P) f)
    (natmod_component alpha beta p i)
    (natmod_component alpha beta p j)
    (natmod_isnatural alpha beta p f)).
Defined.

Definition fun01_pointwise_span_pushout_unmate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  : opyon_0gpd X
      (double_diagonal02 Type J WalkingSpan P)
    $-> opyon_0gpd (pointwise_span_pushout X)
      (diagonal02 Type J P).
Proof.
  snapply Build_Fun01'.
  { exact (nattrans_pointwise_span_pushout_unmate X P). }
  intros alpha beta p.
  exact (natmod_pointwise_span_pushout_unmate X P p).
Defined.

Definition span_pushout_triangle_l
  (X : Fun02 WalkingSpan Type)
  : span_pushout_counit_component (span_pushout X)
      o span_pushout_map (span_pushout_unit_component X)
    == idmap.
Proof.
  snapply Pushout_ind.
  - reflexivity.
  - reflexivity.
  - intros x.
    transport_paths FlFr.
    rewrite !concat_1p, !concat_p1.
    lhs exact (ap_compose
      (span_pushout_map (span_pushout_unit_component X))
      (span_pushout_counit_component (span_pushout X))
      (pglue x)).
    rhs napply ap_idmap.
    rewrite functor_pushout_beta_pglue.
    unfold span_pushout_unit_component.
    unfold span_recdata_to_cocone.
    cbn.
    rewrite concat_1p, inv_V, ap_pp.
    unfold span_pushout_counit_component.
    lhs' exact (whiskerR
      (Pushout_rec_beta_pglue (span_pushout X)
        idmap idmap (fun _ => 1)
        (pushl (fmap X (a := span_center)
          (b := span_left) tt x))) _).
    lhs' exact (concat_1p _).
    lhs' exact (ap_compose pushr
      (Pushout_rec (span_pushout X)
        idmap idmap (fun _ => 1)) (pglue x))^.
    exact (ap_idmap _).
Defined.

Definition span_pushout_triangle_r (P : Type)
  : NatModification
      (A := WalkingSpan) (B := Type)
      (F := diagonal02 Type WalkingSpan P)
      (G := diagonal02 Type WalkingSpan P)
      (nattrans_comp
        (F := diagonal02 Type WalkingSpan P)
        (G := diagonal02 Type WalkingSpan
          (span_pushout (diagonal02 Type WalkingSpan P)))
        (K := diagonal02 Type WalkingSpan P)
        (fmap (diagonal02 Type WalkingSpan)
          (span_pushout_counit_component P))
        (span_pushout_unit_component
          (diagonal02 Type WalkingSpan P)))
      (nattrans_id (diagonal02 Type WalkingSpan P)).
Proof.
  snapply Build_NatModification.
  { intro i.
    destruct i; intro x; reflexivity. }
  intros i j f.
  destruct i, j; destruct f; cbn beta.
  - intros x.
    unfold Cylinder, Square.
    cbn.
    reflexivity.
  - intros x.
    unfold Cylinder, Square.
    cbn.
    rewrite !concat_1p, !concat_p1.
    lhs exact (ap_V (span_pushout_counit_component P) (pglue x)).
    unfold span_pushout_counit_component.
    lhs napply (ap (fun p => p^)).
    { napply Pushout_rec_beta_pglue. }
    reflexivity.
Defined.

Definition gpd_adjunction_span_pushout
  : GpdAdjunction
      fun12_span_pushout
      (fun12_fun22 (fun22_diagonal02 Type WalkingSpan)).
Proof.
  napply (Build_GpdAdjunction_unit_counit
    fun12_span_pushout
    (fun12_fun22 (fun22_diagonal02 Type WalkingSpan))
    nattrans_span_pushout_counit
    nattrans_span_pushout_unit).
  - exact span_pushout_triangle_l.
  - exact span_pushout_triangle_r.
  Unshelve.
  { exact is1functor_span_pushout. }
  exact (is1functor_diagonal02_type WalkingSpan).
Defined.

Global Instance hascolimit02_type_walking_span
  : HasColimit02 Type WalkingSpan.
Proof.
  snapply Build_HasColimit02.
  - exact fun12_span_pushout.
  - exact gpd_adjunction_span_pushout.
Defined.

Definition span_pushout_unit_iscolimit
  (X : Fun02 WalkingSpan Type)
  : IsColimitCocone X (span_pushout X)
      (span_pushout_unit_component X).
Proof.
  intro P.
  exact (cate_isequiv
    (equiv_gpd_adjunction
      fun12_span_pushout
      (fun12_fun22 (fun22_diagonal02 Type WalkingSpan))
      gpd_adjunction_span_pushout X P)).
Defined.

Definition ispushoutsquare_pushout
  {A B C : Type} (f : A -> B) (g : A -> C)
  : IsPushoutSquare f g (@pushl A B C f g) pushr pglue
  := span_pushout_unit_iscolimit
    (fun02_walking_span B A C f g).

Definition span_pushout_unmate_mate
  (X : Fun02 WalkingSpan Type) (P : Type)
  (a : span_pushout X -> P)
  : span_pushout_unmate_component X P
      (nattrans_comp
        (fmap (diagonal02 Type WalkingSpan) a)
        (span_pushout_unit_component X))
    == a.
Proof.
  unfold span_pushout_unmate_component.
  lhs' exact (span_pushout_counit_component P $@L
    span_pushout_map_comp
      (span_pushout_unit_component X)
      (fmap (diagonal02 Type WalkingSpan) a)).
  lhs' exact (cat_assoc_opp
    (span_pushout_map (span_pushout_unit_component X))
    (span_pushout_map (fmap (diagonal02 Type WalkingSpan) a))
    (span_pushout_counit_component P)).
  lhs' exact (isnat nattrans_span_pushout_counit a
    $@R span_pushout_map (span_pushout_unit_component X)).
  lhs' exact (cat_assoc
    (span_pushout_map (span_pushout_unit_component X))
    (span_pushout_counit_component (span_pushout X)) a).
  lhs' exact (a $@L span_pushout_triangle_l X).
  exact (cat_idr a).
Defined.

Definition natmod_pointwise_span_pushout_unmate_mate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  (alpha : pointwise_span_pushout X
    $-> diagonal02 Type J P)
  : nattrans_pointwise_span_pushout_unmate X P
      (nattrans_pointwise_span_pushout_mate X P alpha)
    $== alpha.
Proof.
  snapply Build_NatModification.
  { intro j.
    exact (span_pushout_unmate_mate (X j) P (alpha j)). }
  intros i j f.
  unfold Cylinder.
  snapply Pushout_ind.
  - intro x.
    unfold span_pushout_unmate_mate.
    unfold span_pushout_unmate_naturality.
    unfold natmod_span_pushout_mate_naturality.
    unfold span_pushout_map_homotopy.
    unfold Square.
    cbn beta.
    reflexivity.
  - intro x.
    unfold span_pushout_unmate_mate.
    unfold span_pushout_unmate_naturality.
    unfold natmod_span_pushout_mate_naturality.
    unfold span_pushout_map_homotopy.
    unfold Square.
    cbn beta.
    reflexivity.
  - intro x.
    reflexivity.
Defined.

Definition span_pushout_mate_unmate
  (X : Fun02 WalkingSpan Type) (P : Type)
  (a : X $-> diagonal02 Type WalkingSpan P)
  : nattrans_comp
      (fmap (diagonal02 Type WalkingSpan)
        (span_pushout_unmate_component X P a))
      (span_pushout_unit_component X)
    $== a.
Proof.
  unfold span_pushout_unmate_component.
  lhs' exact (natmod_precompose
    (A := WalkingSpan) (B := Type)
    (K := X)
    (F := diagonal02 Type WalkingSpan (span_pushout X))
    (G := diagonal02 Type WalkingSpan P)
    (span_pushout_unit_component X)
    (natmod_diagonal02_type_comp WalkingSpan
      (span_pushout_map a) (span_pushout_counit_component P))).
  lhs' exact (cat_assoc
    (span_pushout_unit_component X)
    (fmap (diagonal02 Type WalkingSpan) (span_pushout_map a))
    (fmap (diagonal02 Type WalkingSpan)
      (span_pushout_counit_component P))).
  lhs' exact (natmod_postcompose
    (A := WalkingSpan) (B := Type)
    (F := X)
    (G := diagonal02 Type WalkingSpan
      (span_pushout (diagonal02 Type WalkingSpan P)))
    (K := diagonal02 Type WalkingSpan P)
    (fmap (diagonal02 Type WalkingSpan)
      (span_pushout_counit_component P))
    (natmod_inverse (natmod_span_pushout_unit_naturality a))).
  lhs' exact (cat_assoc_opp a
    (span_pushout_unit_component
      (diagonal02 Type WalkingSpan P))
    (fmap (diagonal02 Type WalkingSpan)
      (span_pushout_counit_component P))).
  lhs' exact (natmod_precompose
    (A := WalkingSpan) (B := Type)
    (K := X)
    (F := diagonal02 Type WalkingSpan P)
    (G := diagonal02 Type WalkingSpan P)
    a (span_pushout_triangle_r P)).
  exact (cat_idl a).
Defined.

Definition natmod_pointwise_span_pushout_mate_unmate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  (alpha : X $-> double_diagonal02 Type J WalkingSpan P)
  : nattrans_pointwise_span_pushout_mate X P
      (nattrans_pointwise_span_pushout_unmate X P alpha)
    $== alpha.
Proof.
  snapply Build_NatModification.
  { intro j.
    exact (span_pushout_mate_unmate (X j) P (alpha j)). }
  intros i j f.
  rapply Build_Cylinder_fun02.
  intro w.
  destruct w.
  - intro x.
    unfold span_pushout_mate_unmate.
    unfold natmod_span_pushout_mate_naturality.
    unfold span_pushout_unmate_naturality.
    unfold Cylinder, Square.
    cbn beta.
    reflexivity.
  - intro x.
    unfold span_pushout_mate_unmate.
    unfold natmod_span_pushout_mate_naturality.
    unfold span_pushout_unmate_naturality.
    unfold Cylinder, Square.
    cbn beta.
    reflexivity.
  - intro x.
    unfold span_pushout_mate_unmate.
    unfold natmod_span_pushout_mate_naturality.
    unfold span_pushout_unmate_naturality.
    unfold Cylinder, Square.
    cbn beta.
    reflexivity.
Defined.

Definition equiv_pointwise_span_pushout_mate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type)) (P : Type)
  : opyon_0gpd (pointwise_span_pushout X)
      (diagonal02 Type J P)
    $<~> opyon_0gpd X
      (double_diagonal02 Type J WalkingSpan P).
Proof.
  snapply cate_adjointify.
  - exact (fun01_pointwise_span_pushout_mate X P).
  - exact (fun01_pointwise_span_pushout_unmate X P).
  - exact (natmod_pointwise_span_pushout_unmate_mate X P).
  - exact (natmod_pointwise_span_pushout_mate_unmate X P).
Defined.

Definition natmod_span_pushout_mate_postcompose
  (X : Fun02 WalkingSpan Type) {P Q : Type}
  (a : span_pushout X -> P) (k : P -> Q)
  : nattrans_comp
      (fmap (diagonal02 Type WalkingSpan) (k o a))
      (span_pushout_unit_component X)
    $== nattrans_comp
      (fmap (diagonal02 Type WalkingSpan) k)
      (nattrans_comp
        (fmap (diagonal02 Type WalkingSpan) a)
        (span_pushout_unit_component X)).
Proof.
  lhs' exact (natmod_precompose
    (A := WalkingSpan) (B := Type)
    (K := X)
    (F := diagonal02 Type WalkingSpan (span_pushout X))
    (G := diagonal02 Type WalkingSpan Q)
    (span_pushout_unit_component X)
    (natmod_diagonal02_type_comp WalkingSpan a k)).
  exact (cat_assoc
    (span_pushout_unit_component X)
    (fmap (diagonal02 Type WalkingSpan) a)
    (fmap (diagonal02 Type WalkingSpan) k)).
Defined.

Definition natmod_pointwise_span_pushout_mate_postcompose
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type))
  {P Q : Type} (k : P -> Q)
  (alpha : pointwise_span_pushout X
    $-> diagonal02 Type J P)
  : nattrans_pointwise_span_pushout_mate X Q
      (nattrans_comp
        (fmap (diagonal02 Type J) k) alpha)
    $== nattrans_comp
      (fmap (double_diagonal02 Type J WalkingSpan) k)
      (nattrans_pointwise_span_pushout_mate X P alpha).
Proof.
  snapply Build_NatModification.
  { intro j.
    exact (natmod_span_pushout_mate_postcompose
      (X j) (alpha j) k). }
  intros i j f.
  rapply Build_Cylinder_fun02.
  intro w.
  destruct w.
  - intro x.
    unfold natmod_span_pushout_mate_postcompose.
    unfold natmod_span_pushout_mate_naturality.
    unfold Cylinder, Square.
    cbn beta.
    reflexivity.
  - intro x.
    unfold natmod_span_pushout_mate_postcompose.
    unfold natmod_span_pushout_mate_naturality.
    unfold Cylinder, Square.
    cbn beta.
    reflexivity.
  - intro x.
    unfold natmod_span_pushout_mate_postcompose.
    unfold natmod_span_pushout_mate_naturality.
    unfold Cylinder, Square.
    cbn beta.
    reflexivity.
Defined.

Definition natequiv_pointwise_span_pushout_mate
  {J : Type} `{IsGraph J}
  (X : Fun02 J (Fun02 WalkingSpan Type))
  : NatEquiv
      (cocone02 (pointwise_span_pushout X))
      (opyon_0gpd X o
        double_diagonal02 Type J WalkingSpan).
Proof.
  snapply Build_NatEquiv.
  { exact (equiv_pointwise_span_pushout_mate X). }
  snapply Build_Is1Natural.
  intros P Q k alpha.
  exact (natmod_pointwise_span_pushout_mate_postcompose
    X k alpha).
Defined.

(** The specialized pointwise result is enough for Fubini.  In particular, it avoids asking the pushout construction to define a full [Fun22] action on arbitrary pointwise 3-cells. *)
Definition natequiv_double_cocone_columns_type
  (X : Fun02 WalkingSpan
    (Fun02 WalkingSpan Type))
  : NatEquiv
      (opyon_0gpd X o
        double_diagonal02 Type WalkingSpan WalkingSpan)
      (double_cocone_columns Type
        WalkingSpan WalkingSpan X)
  := natequiv_inverse
    (natequiv_postwhisker
      (A := Type)
      (B := Fun02 WalkingSpan (Fun02 WalkingSpan Type))
      (C := ZeroGpd)
      (F := swapped_double_diagonal02 Type
        WalkingSpan WalkingSpan)
      (G := double_diagonal02 Type
        WalkingSpan WalkingSpan)
      (opyon_0gpd X)
      (natequiv_diagonal_interchange02_type
        WalkingSpan WalkingSpan)).

Definition iterated_span_pushout_isdouble_columns
  (X : Fun02 WalkingSpan
    (Fun02 WalkingSpan Type))
  : IsDoubleColimitColumns Type WalkingSpan WalkingSpan X
      (iterated_span_pushout X)
  := natequiv_compose
    (span_pushout_iscolimit (pointwise_span_pushout X))
    (natequiv_compose
      (natequiv_pointwise_span_pushout_mate X)
      (natequiv_double_cocone_columns_type X)).

Definition iterated_span_pushout_swapped
  (X : Fun02 WalkingSpan
    (Fun02 WalkingSpan Type))
  : Type
  := iterated_span_pushout
      (swap_fun02 WalkingSpan WalkingSpan Type X).

Definition iterated_span_pushout_isdouble_rows
  (X : Fun02 WalkingSpan
    (Fun02 WalkingSpan Type))
  : IsDoubleColimitRows Type WalkingSpan WalkingSpan X
      (iterated_span_pushout_swapped X)
  := natequiv_compose
    (iterated_span_pushout_isdouble_columns
      (swap_fun02 WalkingSpan WalkingSpan Type X))
    (natequiv_double_cocone_diagonal_interchange
      Type WalkingSpan WalkingSpan X).

Definition equiv_iterated_span_pushout_fubini
  (X : Fun02 WalkingSpan
    (Fun02 WalkingSpan Type))
  : iterated_span_pushout X
    $<~> iterated_span_pushout_swapped X
  := equiv_colimit_fubini
    Type WalkingSpan WalkingSpan X
    (iterated_span_pushout_isdouble_rows X)
    (iterated_span_pushout_isdouble_columns X).

*)
(*

(** Rotating the boundary of a square after exposing one path at each
    corner.  This is the path-groupoid calculation used by the
    concrete pushout 3-by-3 map. *)
Definition concat_3_by_3
  {A : Type} {x0 x1 x2 x3 x4 y1 y2 y3 : A}
  (a : x0 = x1) (b : x1 = x2) (c : x3 = x2) (d : x3 = x4)
  (e : x0 = y1) (f : y1 = y2) (g : y2 = y3) (h : x4 = y3)
  (s : ((a^ @ e) @ f) @ g = b @ ((c^ @ d) @ h))
  : ((a @ b) @ c^) @ d = e @ ((f @ g) @ h^).
Proof.
  destruct a, b, c, d, e, f, g.
  cbn in s.
  rewrite !concat_1p in s.
  destruct s.
  reflexivity.
Defined.

Section PushoutsInType.
  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : f01 $o f12 $== f10 $o f21)
    (H13 : f03 $o f12 $== f14 $o f23)
    (H31 : f41 $o f32 $== f30 $o f21)
    (H33 : f43 $o f32 $== f34 $o f23).

  Local Definition pushout_columns_left
    := functor_pushout f21 f01 f41 H11 H31.

  Local Definition pushout_columns_right
    := functor_pushout f23 f03 f43 H13 H33.

  Local Definition pushout_rows_left
    := functor_pushout f12 f10 f14 H11^$ H13^$.

  Local Definition pushout_rows_right
    := functor_pushout f32 f30 f34 H31^$ H33^$.

  Local Definition pushout_3_by_3_diagram
    : Fun02 WalkingSpan (Fun02 WalkingSpan Type).
  Proof.
    snapply (fun02_walking_span
      (A := Fun02 WalkingSpan Type)).
    - exact (fun02_walking_span A00 A02 A04 f01 f03).
    - exact (fun02_walking_span A20 A22 A24 f21 f23).
    - exact (fun02_walking_span A40 A42 A44 f41 f43).
    - snapply Build_NatTrans.
      { intro i.
        destruct i.
        - exact f10.
        - exact f12.
        - exact f14. }
      snapply Build_Is1Natural.
      intros i j f.
      destruct i, j; destruct f.
      + exact H11^$.
      + exact H13^$.
    - snapply Build_NatTrans.
      { intro i.
        destruct i.
        - exact f30.
        - exact f32.
        - exact f34. }
      snapply Build_Is1Natural.
      intros i j f.
      destruct i, j; destruct f.
      + exact H31^$.
      + exact H33^$.
  Defined.

  Local Definition pushout_3_by_3_rows
    := Pushout pushout_rows_left pushout_rows_right.

  Local Definition pushout_3_by_3_top
    : Pushout f01 f03 -> pushout_3_by_3_rows
    := pushl.

  Local Definition pushout_3_by_3_bottom
    : Pushout f41 f43 -> pushout_3_by_3_rows
    := pushr.

  Local Definition pushout_3_by_3_in00
    : A00 -> pushout_3_by_3_rows
    := pushout_3_by_3_top o pushl.

  Local Definition pushout_3_by_3_in04
    : A04 -> pushout_3_by_3_rows
    := pushout_3_by_3_top o pushr.

  Local Definition pushout_3_by_3_in40
    : A40 -> pushout_3_by_3_rows
    := pushout_3_by_3_bottom o pushl.

  Local Definition pushout_3_by_3_in44
    : A44 -> pushout_3_by_3_rows
    := pushout_3_by_3_bottom o pushr.

  Local Definition pushout_3_by_3_rows_left_beta_pglue (x : A22)
    : ap (pushout_3_by_3_top o pushout_rows_left) (pglue x)
      = (((ap pushout_3_by_3_in00 (H11 x))^
        @ ap pushl (pglue (f12 x)))
        @ ap pushout_3_by_3_in04 (H13 x)).
  Proof.
    lhs exact (ap_compose pushout_rows_left pushout_3_by_3_top
      (pglue x)).
    rewrite functor_pushout_beta_pglue.
    rewrite !ap_pp.
    rewrite !ap_V.
    rewrite !inv_V.
    unfold pushout_3_by_3_in00.
    unfold pushout_3_by_3_in04.
    rewrite (ap_compose pushl pushout_3_by_3_top (H11 x)).
    rewrite (ap_compose pushr pushout_3_by_3_top (H13 x)).
    reflexivity.
  Defined.

  Local Definition pushout_3_by_3_rows_right_beta_pglue (x : A22)
    : ap (pushout_3_by_3_bottom o pushout_rows_right) (pglue x)
      = (((ap pushout_3_by_3_in40 (H31 x))^
        @ ap pushr (pglue (f32 x)))
        @ ap pushout_3_by_3_in44 (H33 x)).
  Proof.
    lhs exact (ap_compose pushout_rows_right pushout_3_by_3_bottom
      (pglue x)).
    rewrite functor_pushout_beta_pglue.
    rewrite !ap_pp.
    rewrite !ap_V.
    rewrite !inv_V.
    unfold pushout_3_by_3_in40.
    unfold pushout_3_by_3_in44.
    rewrite (ap_compose pushl pushout_3_by_3_bottom (H31 x)).
    rewrite (ap_compose pushr pushout_3_by_3_bottom (H33 x)).
    reflexivity.
  Defined.

  Definition pushout_3_by_3_to_left
    : Pushout f10 f30 -> pushout_3_by_3_rows.
  Proof.
    snapply Pushout_rec.
    - exact pushout_3_by_3_in00.
    - exact pushout_3_by_3_in40.
    - exact (fun x => pglue (pushl x)).
  Defined.

  Definition pushout_3_by_3_to_right
    : Pushout f14 f34 -> pushout_3_by_3_rows.
  Proof.
    snapply Pushout_rec.
    - exact pushout_3_by_3_in04.
    - exact pushout_3_by_3_in44.
    - exact (fun x => pglue (pushr x)).
  Defined.

  Local Definition pushout_3_by_3_to_left_beta_pushl (x : A00)
    : pushout_3_by_3_to_left (pushl x) = pushout_3_by_3_in00 x
    := 1.

  Local Definition pushout_3_by_3_to_left_beta_pushr (x : A40)
    : pushout_3_by_3_to_left (pushr x) = pushout_3_by_3_in40 x
    := 1.

  Local Definition pushout_3_by_3_to_right_beta_pushl (x : A04)
    : pushout_3_by_3_to_right (pushl x) = pushout_3_by_3_in04 x
    := 1.

  Local Definition pushout_3_by_3_to_right_beta_pushr (x : A44)
    : pushout_3_by_3_to_right (pushr x) = pushout_3_by_3_in44 x
    := 1.

  Definition pushout_3_by_3_to_left_beta_pglue (x : A20)
    : ap pushout_3_by_3_to_left (pglue x) = pglue (pushl x).
  Proof.
    napply Pushout_rec_beta_pglue.
  Defined.

  Definition pushout_3_by_3_to_right_beta_pglue (x : A24)
    : ap pushout_3_by_3_to_right (pglue x) = pglue (pushr x).
  Proof.
    napply Pushout_rec_beta_pglue.
  Defined.

  Local Definition pushout_3_by_3_columns_left_beta_pglue (x : A22)
    : ap (pushout_3_by_3_to_left o pushout_columns_left) (pglue x)
      = ((ap pushout_3_by_3_in00 (H11 x)
        @ pglue (pushl (f21 x)))
        @ (ap pushout_3_by_3_in40 (H31 x))^).
  Proof.
    lhs exact (ap_compose pushout_columns_left
      pushout_3_by_3_to_left (pglue x)).
    rewrite functor_pushout_beta_pglue.
    rewrite !ap_pp.
    rewrite pushout_3_by_3_to_left_beta_pglue.
    rewrite !ap_V.
    rewrite <- (ap_compose pushl
      pushout_3_by_3_to_left (H11 x)).
    rewrite <- (ap_compose pushr
      pushout_3_by_3_to_left (H31 x)).
    rewrite (ap_homotopic
      pushout_3_by_3_to_left_beta_pushl (H11 x)).
    rewrite (ap_homotopic
      pushout_3_by_3_to_left_beta_pushr (H31 x)).
    rewrite !concat_1p.
    rewrite !concat_p1.
    reflexivity.
  Defined.

  Local Definition pushout_3_by_3_columns_right_beta_pglue (x : A22)
    : ap (pushout_3_by_3_to_right o pushout_columns_right) (pglue x)
      = ((ap pushout_3_by_3_in04 (H13 x)
        @ pglue (pushr (f23 x)))
        @ (ap pushout_3_by_3_in44 (H33 x))^).
  Proof.
    lhs exact (ap_compose pushout_columns_right
      pushout_3_by_3_to_right (pglue x)).
    rewrite functor_pushout_beta_pglue.
    rewrite !ap_pp.
    rewrite pushout_3_by_3_to_right_beta_pglue.
    rewrite !ap_V.
    rewrite <- (ap_compose pushl
      pushout_3_by_3_to_right (H13 x)).
    rewrite <- (ap_compose pushr
      pushout_3_by_3_to_right (H33 x)).
    rewrite (ap_homotopic
      pushout_3_by_3_to_right_beta_pushl (H13 x)).
    rewrite (ap_homotopic
      pushout_3_by_3_to_right_beta_pushr (H33 x)).
    rewrite !concat_1p.
    rewrite !concat_p1.
    reflexivity.
  Defined.

  Definition pushout_3_by_3_to_glue
    : pushout_3_by_3_to_left o pushout_columns_left
      == pushout_3_by_3_to_right o pushout_columns_right.
  Proof.
    snapply Pushout_ind.
    - exact (fun x => ap pushl (pglue x)).
    - exact (fun x => ap pushr (pglue x)).
    - intro x.
      transport_paths FlFr.
      rewrite pushout_3_by_3_columns_left_beta_pglue.
      rewrite pushout_3_by_3_columns_right_beta_pglue.
      napply concat_3_by_3.
      exact (whiskerR
        (pushout_3_by_3_rows_left_beta_pglue x)^
        (pglue (pushr (f23 x)))
        @ concat_Ap (pglue
          (f := pushout_rows_left)
          (g := pushout_rows_right)) (pglue x)
        @ whiskerL (pglue (pushl (f21 x)))
          (pushout_3_by_3_rows_right_beta_pglue x)).
  Defined.

  Definition pushout_3_by_3_to_glue_beta_pushl (x : A02)
    : pushout_3_by_3_to_glue (pushl x) = ap pushl (pglue x)
    := 1.

  Definition pushout_3_by_3_to_glue_beta_pushr (x : A42)
    : pushout_3_by_3_to_glue (pushr x) = ap pushr (pglue x)
    := 1.

  Definition pushout_3_by_3_to
    : Pushout pushout_columns_left pushout_columns_right
      -> pushout_3_by_3_rows.
  Proof.
    snapply Pushout_rec.
    - exact pushout_3_by_3_to_left.
    - exact pushout_3_by_3_to_right.
    - exact pushout_3_by_3_to_glue.
  Defined.

  Definition pushout_3_by_3_to_beta_pushl
    : pushout_3_by_3_to o pushl == pushout_3_by_3_to_left
    := fun _ => 1.

  Definition pushout_3_by_3_to_beta_pushr
    : pushout_3_by_3_to o pushr == pushout_3_by_3_to_right
    := fun _ => 1.

  Definition pushout_3_by_3_to_beta_pglue
    (x : Pushout f12 f32)
    : ap pushout_3_by_3_to (pglue x) = pushout_3_by_3_to_glue x.
  Proof.
    napply Pushout_rec_beta_pglue.
  Defined.

  (** The concrete 3-by-3 statement: taking the three column pushouts followed by their row pushout agrees with taking the three row pushouts followed by their column pushout. *)
  Definition pushout_3_by_3_statement : Type
    := Pushout pushout_columns_left pushout_columns_right
      $<~> Pushout pushout_rows_left pushout_rows_right.

  Definition pushout_3_by_3
    : pushout_3_by_3_statement.
  Proof.
    exact (equiv_inverse
      (equiv_iterated_span_pushout_fubini
        pushout_3_by_3_diagram)).
  Defined.

  (** After applying the 0-groupoid-valued Yoneda lemma and the pushout recursion equivalence, this is the only remaining computation. *)
  Definition pushout_3_by_3_recdata_statement : Type
    := NatEquiv
      (pushoutrecdata_0gpd_fun
        pushout_columns_left pushout_columns_right)
      (pushoutrecdata_0gpd_fun pushout_rows_left pushout_rows_right).

  Definition pushout_3_by_3_of_recdata
    (e : pushout_3_by_3_recdata_statement)
    : pushout_3_by_3_statement.
  Proof.
    napply (opyon_equiv_0gpd (A := Type)).
    exact (natequiv_compose
      (pushout_rec_natequiv pushout_columns_left pushout_columns_right)
      (natequiv_compose (natequiv_inverse e)
        (pushout_rec_inv_natequiv
          pushout_rows_left pushout_rows_right))).
  Defined.
End PushoutsInType.

Section PushoutsInTypeEquiv.
  Context
    {A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type}
    {f01 : A02 $-> A00} {f03 : A02 $-> A04}
    {f10 : A20 $-> A00} {f12 : A22 $-> A02} {f14 : A24 $-> A04}
    {f21 : A22 $-> A20} {f23 : A22 $-> A24}
    {f30 : A20 $-> A40} {f32 : A22 $-> A42} {f34 : A24 $-> A44}
    {f41 : A42 $-> A40} {f43 : A42 $-> A44}
    (H11 : f01 $o f12 $== f10 $o f21)
    (H13 : f03 $o f12 $== f14 $o f23)
    (H31 : f41 $o f32 $== f30 $o f21)
    (H33 : f43 $o f32 $== f34 $o f23).

  Local Definition pushout_equiv_columns_left
    := functor_pushout f21 f01 f41 H11 H31.

  Local Definition pushout_equiv_columns_right
    := functor_pushout f23 f03 f43 H13 H33.

  Local Definition pushout_equiv_rows_left
    := functor_pushout f12 f10 f14 H11^$ H13^$.

  Local Definition pushout_equiv_rows_right
    := functor_pushout f32 f30 f34 H31^$ H33^$.

  Local Definition pushout_double_columns_left
    := functor_pushout f21 f01 f41 (H11^$)^$ (H31^$)^$.

  Local Definition pushout_double_columns_right
    := functor_pushout f23 f03 f43 (H13^$)^$ (H33^$)^$.

  Local Definition pushout_double_columns_left_homotopy
    : pushout_double_columns_left == pushout_equiv_columns_left.
  Proof.
    snapply Pushout_ind.
    - reflexivity.
    - reflexivity.
    - intro x.
      transport_paths FlFr.
      rewrite concat_p1, concat_1p.
      rewrite !functor_pushout_beta_pglue.
      rewrite !inv_V.
      change ((H11^$)^$ x) with ((H11 x)^)^.
      rewrite inv_V.
      reflexivity.
  Defined.

  Local Definition pushout_double_columns_right_homotopy
    : pushout_double_columns_right == pushout_equiv_columns_right.
  Proof.
    snapply Pushout_ind.
    - reflexivity.
    - reflexivity.
    - intro x.
      transport_paths FlFr.
      rewrite concat_p1, concat_1p.
      rewrite !functor_pushout_beta_pglue.
      rewrite !inv_V.
      change ((H13^$)^$ x) with ((H13 x)^)^.
      rewrite inv_V.
      reflexivity.
  Defined.

  Local Definition pushout_double_columns_left_homotopy_beta_pushl
    (x : A02)
    : pushout_double_columns_left_homotopy (pushl x) = 1
    := 1.

  Local Definition pushout_double_columns_left_homotopy_beta_pushr
    (x : A42)
    : pushout_double_columns_left_homotopy (pushr x) = 1
    := 1.

  Local Definition pushout_double_columns_right_homotopy_beta_pushl
    (x : A02)
    : pushout_double_columns_right_homotopy (pushl x) = 1
    := 1.

  Local Definition pushout_double_columns_right_homotopy_beta_pushr
    (x : A42)
    : pushout_double_columns_right_homotopy (pushr x) = 1
    := 1.

  Local Definition pushout_3_by_3_transposed
    : Pushout pushout_equiv_rows_left pushout_equiv_rows_right
      -> Pushout pushout_double_columns_left pushout_double_columns_right
    := pushout_3_by_3_to
      (A00 := A00) (A02 := A20) (A04 := A40)
      (A20 := A02) (A22 := A22) (A24 := A42)
      (A40 := A04) (A42 := A24) (A44 := A44)
      (f01 := f10) (f03 := f30)
      (f10 := f01) (f12 := f21) (f14 := f41)
      (f21 := f12) (f23 := f32)
      (f30 := f03) (f32 := f23) (f34 := f43)
      (f41 := f14) (f43 := f34)
      H11^$ H31^$ H13^$ H33^$.

  Local Definition pushout_3_by_3_transposed_glue
    := pushout_3_by_3_to_glue
      (A00 := A00) (A02 := A20) (A04 := A40)
      (A20 := A02) (A22 := A22) (A24 := A42)
      (A40 := A04) (A42 := A24) (A44 := A44)
      (f01 := f10) (f03 := f30)
      (f10 := f01) (f12 := f21) (f14 := f41)
      (f21 := f12) (f23 := f32)
      (f30 := f03) (f32 := f23) (f34 := f43)
      (f41 := f14) (f43 := f34)
      H11^$ H31^$ H13^$ H33^$.

  Local Definition pushout_3_by_3_transposed_beta_pglue
    (x : Pushout f21 f23)
    : ap pushout_3_by_3_transposed (pglue x)
      = pushout_3_by_3_transposed_glue x.
  Proof.
    unfold pushout_3_by_3_transposed.
    unfold pushout_3_by_3_transposed_glue.
    napply pushout_3_by_3_to_beta_pglue.
  Defined.

  Local Definition pushout_3_by_3_transposed_glue_beta_pushl
    (x : A20)
    : pushout_3_by_3_transposed_glue (pushl x)
      = ap pushl (pglue x).
  Proof.
    unfold pushout_3_by_3_transposed_glue.
    napply pushout_3_by_3_to_glue_beta_pushl.
  Defined.

  Local Definition pushout_3_by_3_transposed_glue_beta_pushr
    (x : A24)
    : pushout_3_by_3_transposed_glue (pushr x)
      = ap pushr (pglue x).
  Proof.
    unfold pushout_3_by_3_transposed_glue.
    napply pushout_3_by_3_to_glue_beta_pushr.
  Defined.

  Local Definition pushout_3_by_3_transposed_left
    := pushout_3_by_3_to_left
      (A00 := A00) (A02 := A20) (A04 := A40)
      (A20 := A02) (A22 := A22) (A24 := A42)
      (A40 := A04) (A42 := A24) (A44 := A44)
      (f01 := f10) (f03 := f30)
      (f10 := f01) (f12 := f21) (f14 := f41)
      (f21 := f12) (f23 := f32)
      (f30 := f03) (f32 := f23) (f34 := f43)
      (f41 := f14) (f43 := f34)
      H11^$ H31^$ H13^$ H33^$.

  Local Definition pushout_3_by_3_transposed_right
    := pushout_3_by_3_to_right
      (A00 := A00) (A02 := A20) (A04 := A40)
      (A20 := A02) (A22 := A22) (A24 := A42)
      (A40 := A04) (A42 := A24) (A44 := A44)
      (f01 := f10) (f03 := f30)
      (f10 := f01) (f12 := f21) (f14 := f41)
      (f21 := f12) (f23 := f32)
      (f30 := f03) (f32 := f23) (f34 := f43)
      (f41 := f14) (f43 := f34)
      H11^$ H31^$ H13^$ H33^$.

  Local Definition pushout_3_by_3_transposed_beta_pushl
    : pushout_3_by_3_transposed o pushl
      == pushout_3_by_3_transposed_left.
  Proof.
    unfold pushout_3_by_3_transposed.
    unfold pushout_3_by_3_transposed_left.
    napply pushout_3_by_3_to_beta_pushl.
  Defined.

  Local Definition pushout_3_by_3_transposed_beta_pushr
    : pushout_3_by_3_transposed o pushr
      == pushout_3_by_3_transposed_right.
  Proof.
    unfold pushout_3_by_3_transposed.
    unfold pushout_3_by_3_transposed_right.
    napply pushout_3_by_3_to_beta_pushr.
  Defined.

  Local Definition pushout_3_by_3_transposed_left_beta_pglue
    (x : A02)
    : ap pushout_3_by_3_transposed_left (pglue x)
      = pglue (pushl x).
  Proof.
    unfold pushout_3_by_3_transposed_left.
    napply pushout_3_by_3_to_left_beta_pglue.
  Defined.

  Local Definition pushout_3_by_3_transposed_right_beta_pglue
    (x : A42)
    : ap pushout_3_by_3_transposed_right (pglue x)
      = pglue (pushr x).
  Proof.
    unfold pushout_3_by_3_transposed_right.
    napply pushout_3_by_3_to_right_beta_pglue.
  Defined.

  Local Definition pushout_3_by_3_from_correction
    : Pushout pushout_double_columns_left pushout_double_columns_right
      -> Pushout pushout_equiv_columns_left pushout_equiv_columns_right.
  Proof.
    snapply functor_pushout.
    - exact idmap.
    - exact idmap.
    - exact idmap.
    - exact pushout_double_columns_left_homotopy.
    - exact pushout_double_columns_right_homotopy.
  Defined.

  Local Definition pushout_3_by_3_from_correction_beta_pushl
    : pushout_3_by_3_from_correction o pushl == pushl
    := fun _ => 1.

  Local Definition pushout_3_by_3_from_correction_beta_pushr
    : pushout_3_by_3_from_correction o pushr == pushr
    := fun _ => 1.

  Local Definition pushout_3_by_3_from_correction_beta_pglue_pushl
    (x : A02)
    : ap pushout_3_by_3_from_correction (pglue (pushl x))
      = pglue (pushl x).
  Proof.
    rewrite functor_pushout_beta_pglue.
    rewrite pushout_double_columns_left_homotopy_beta_pushl.
    rewrite pushout_double_columns_right_homotopy_beta_pushl.
    rewrite !ap_1, concat_1p, concat_p1.
    reflexivity.
  Defined.

  Local Definition pushout_3_by_3_from_correction_beta_pglue_pushr
    (x : A42)
    : ap pushout_3_by_3_from_correction (pglue (pushr x))
      = pglue (pushr x).
  Proof.
    rewrite functor_pushout_beta_pglue.
    rewrite pushout_double_columns_left_homotopy_beta_pushr.
    rewrite pushout_double_columns_right_homotopy_beta_pushr.
    rewrite !ap_1, concat_1p, concat_p1.
    reflexivity.
  Defined.

  (** The reverse comparison is the transposed comparison followed by
      the canonical double-inverse correction. *)
  Definition pushout_3_by_3_from
    : Pushout pushout_equiv_rows_left pushout_equiv_rows_right
      -> Pushout pushout_equiv_columns_left pushout_equiv_columns_right
    := pushout_3_by_3_from_correction o pushout_3_by_3_transposed.

  Local Definition pushout_3_by_3_forward
    : Pushout pushout_equiv_columns_left pushout_equiv_columns_right
      -> Pushout pushout_equiv_rows_left pushout_equiv_rows_right
    := pushout_3_by_3_to H11 H13 H31 H33.

  Local Definition pushout_3_by_3_forward_beta_pushl
    : pushout_3_by_3_forward o pushl
      == pushout_3_by_3_to_left H11 H13 H31 H33
    := pushout_3_by_3_to_beta_pushl H11 H13 H31 H33.

  Local Definition pushout_3_by_3_forward_beta_pushr
    : pushout_3_by_3_forward o pushr
      == pushout_3_by_3_to_right H11 H13 H31 H33
    := pushout_3_by_3_to_beta_pushr H11 H13 H31 H33.

  Local Definition pushout_3_by_3_forward_glue
    := pushout_3_by_3_to_glue H11 H13 H31 H33.

  Local Definition pushout_3_by_3_forward_beta_pglue
    (x : Pushout f12 f32)
    : ap pushout_3_by_3_forward (pglue x)
      = pushout_3_by_3_forward_glue x
    := pushout_3_by_3_to_beta_pglue H11 H13 H31 H33 x.

  Local Definition pushout_3_by_3_forward_glue_beta_pushl
    (x : A02)
    : pushout_3_by_3_forward_glue (pushl x)
      = ap pushl (pglue x)
    := pushout_3_by_3_to_glue_beta_pushl H11 H13 H31 H33 x.

  Local Definition pushout_3_by_3_forward_glue_beta_pushr
    (x : A42)
    : pushout_3_by_3_forward_glue (pushr x)
      = ap pushr (pglue x)
    := pushout_3_by_3_to_glue_beta_pushr H11 H13 H31 H33 x.

  Local Definition pushout_3_by_3_from_to_left_glue (x : A20)
    : DPath
        (fun w => pushout_3_by_3_from
          (pushout_3_by_3_forward (pushl w)) = pushl w)
        (pglue x) 1 1.
  Proof.
    transport_paths (transport_paths_FlFr
      (f := fun w => pushout_3_by_3_from
        (pushout_3_by_3_forward (pushl w)))
      (g := fun w => pushl w)).
    rewrite concat_p1, concat_1p.
    change (ap
      ((pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed)
        o (pushout_3_by_3_forward o pushl))
      (pglue x) = ap pushl (pglue x)).
    rewrite (ap_compose
      (pushout_3_by_3_forward o pushl)
      (pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed) (pglue x)).
    rewrite (ap_homotopic
      pushout_3_by_3_forward_beta_pushl (pglue x)).
    rewrite concat_1p, concat_p1.
    rewrite pushout_3_by_3_to_left_beta_pglue.
    rewrite (ap_compose pushout_3_by_3_transposed
      pushout_3_by_3_from_correction (pglue (pushl x))).
    rewrite pushout_3_by_3_transposed_beta_pglue.
    rewrite pushout_3_by_3_transposed_glue_beta_pushl.
    rewrite <- (ap_compose pushl
      pushout_3_by_3_from_correction (pglue x)).
    rewrite (ap_homotopic
      pushout_3_by_3_from_correction_beta_pushl (pglue x)).
    rewrite concat_1p, concat_p1.
    reflexivity.
  Defined.

  Local Definition pushout_3_by_3_from_to_left
    : pushout_3_by_3_from o pushout_3_by_3_forward o pushl == pushl.
  Proof.
    snapply Pushout_ind.
    - reflexivity.
    - reflexivity.
    - exact pushout_3_by_3_from_to_left_glue.
  Defined.

  Local Definition pushout_3_by_3_from_to_right_glue (x : A24)
    : DPath
        (fun w => pushout_3_by_3_from
          (pushout_3_by_3_forward (pushr w)) = pushr w)
        (pglue x) 1 1.
  Proof.
    transport_paths (transport_paths_FlFr
      (f := fun w => pushout_3_by_3_from
        (pushout_3_by_3_forward (pushr w)))
      (g := fun w => pushr w)).
    rewrite concat_p1, concat_1p.
    change (ap
      ((pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed)
        o (pushout_3_by_3_forward o pushr))
      (pglue x) = ap pushr (pglue x)).
    rewrite (ap_compose
      (pushout_3_by_3_forward o pushr)
      (pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed) (pglue x)).
    rewrite (ap_homotopic
      pushout_3_by_3_forward_beta_pushr (pglue x)).
    rewrite concat_1p, concat_p1.
    rewrite pushout_3_by_3_to_right_beta_pglue.
    rewrite (ap_compose pushout_3_by_3_transposed
      pushout_3_by_3_from_correction (pglue (pushr x))).
    rewrite pushout_3_by_3_transposed_beta_pglue.
    rewrite pushout_3_by_3_transposed_glue_beta_pushr.
    rewrite <- (ap_compose pushr
      pushout_3_by_3_from_correction (pglue x)).
    rewrite (ap_homotopic
      pushout_3_by_3_from_correction_beta_pushr (pglue x)).
    rewrite concat_1p, concat_p1.
    reflexivity.
  Defined.

  Local Definition pushout_3_by_3_from_to_right
    : pushout_3_by_3_from o pushout_3_by_3_forward o pushr == pushr.
  Proof.
    snapply Pushout_ind.
    - reflexivity.
    - reflexivity.
    - exact pushout_3_by_3_from_to_right_glue.
  Defined.

  Local Definition pushout_3_by_3_from_to_left_beta_pglue (x : A20)
    : apD pushout_3_by_3_from_to_left (pglue x)
      = pushout_3_by_3_from_to_left_glue x.
  Proof.
    napply Pushout_ind_beta_pglue.
  Defined.

  Local Definition pushout_3_by_3_from_to_right_beta_pglue (x : A24)
    : apD pushout_3_by_3_from_to_right (pglue x)
      = pushout_3_by_3_from_to_right_glue x.
  Proof.
    napply Pushout_ind_beta_pglue.
  Defined.

  Local Definition pushout_3_by_3_from_to_left_beta_pushl (x : A00)
    : pushout_3_by_3_from_to_left (pushl x) = 1
    := 1.

  Local Definition pushout_3_by_3_from_to_left_beta_pushr (x : A40)
    : pushout_3_by_3_from_to_left (pushr x) = 1
    := 1.

  Local Definition pushout_3_by_3_from_to_right_beta_pushl (x : A04)
    : pushout_3_by_3_from_to_right (pushl x) = 1
    := 1.

  Local Definition pushout_3_by_3_from_to_right_beta_pushr (x : A44)
    : pushout_3_by_3_from_to_right (pushr x) = 1
    := 1.

  Local Definition pushout_3_by_3_from_to_top (x : A02)
    : PathSquare
        (ap (pushout_3_by_3_from o pushout_3_by_3_forward)
          (pglue (pushl x)))
        (pglue (pushl x))
        (pushout_3_by_3_from_to_left (pushl (f01 x)))
        (pushout_3_by_3_from_to_right (pushl (f03 x))).
  Proof.
    apply sq_path.
    rewrite pushout_3_by_3_from_to_right_beta_pushl.
    rewrite pushout_3_by_3_from_to_left_beta_pushl.
    rewrite concat_p1, concat_1p.
    change (ap
      ((pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed)
        o pushout_3_by_3_forward)
      (pglue (pushl x)) = pglue (pushl x)).
    rewrite (ap_compose pushout_3_by_3_forward
      (pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed) (pglue (pushl x))).
    rewrite pushout_3_by_3_forward_beta_pglue.
    rewrite pushout_3_by_3_forward_glue_beta_pushl.
    rewrite (ap_compose pushout_3_by_3_transposed
      pushout_3_by_3_from_correction (ap pushl (pglue x))).
    rewrite <- (ap_compose pushl
      pushout_3_by_3_transposed (pglue x)).
    rewrite (ap_homotopic
      pushout_3_by_3_transposed_beta_pushl (pglue x)).
    rewrite concat_1p, concat_p1.
    rewrite pushout_3_by_3_transposed_left_beta_pglue.
    rewrite pushout_3_by_3_from_correction_beta_pglue_pushl.
    reflexivity.
  Defined.

  Local Definition pushout_3_by_3_from_to_bottom (x : A42)
    : PathSquare
        (ap (pushout_3_by_3_from o pushout_3_by_3_forward)
          (pglue (pushr x)))
        (pglue (pushr x))
        (pushout_3_by_3_from_to_left (pushr (f41 x)))
        (pushout_3_by_3_from_to_right (pushr (f43 x))).
  Proof.
    apply sq_path.
    rewrite pushout_3_by_3_from_to_right_beta_pushr.
    rewrite pushout_3_by_3_from_to_left_beta_pushr.
    rewrite concat_p1, concat_1p.
    change (ap
      ((pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed)
        o pushout_3_by_3_forward)
      (pglue (pushr x)) = pglue (pushr x)).
    rewrite (ap_compose pushout_3_by_3_forward
      (pushout_3_by_3_from_correction
        o pushout_3_by_3_transposed) (pglue (pushr x))).
    rewrite pushout_3_by_3_forward_beta_pglue.
    rewrite pushout_3_by_3_forward_glue_beta_pushr.
    rewrite (ap_compose pushout_3_by_3_transposed
      pushout_3_by_3_from_correction (ap pushr (pglue x))).
    rewrite <- (ap_compose pushr
      pushout_3_by_3_transposed (pglue x)).
    rewrite (ap_homotopic
      pushout_3_by_3_transposed_beta_pushr (pglue x)).
    rewrite concat_1p, concat_p1.
    rewrite pushout_3_by_3_transposed_right_beta_pglue.
    rewrite pushout_3_by_3_from_correction_beta_pglue_pushr.
    reflexivity.
  Defined.

End PushoutsInTypeEquiv.
*)
