Require Import Basics.Equivalences Basics.Overture Basics.PathGroupoids
  Basics.Tactics.
Require Import Types.Paths Colimits.Pushout.
Require Import WildCat.Core WildCat.NatTrans WildCat.FunctorCat.
Require Import WildCat.Equiv WildCat.EquivGpd WildCat.Universe.
Require Import WildCat.Yoneda WildCat.ZeroGroupoid WildCat.LimitsScratch.

Set Typeclasses Depth 4.

(** * Scratch work on pushouts in [Type] *)

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

  (** The concrete 3-by-3 statement: taking the three column pushouts followed by their row pushout agrees with taking the three row pushouts followed by their column pushout. *)
  Definition pushout_3_by_3_statement : Type
    := Pushout pushout_columns_left pushout_columns_right
      $<~> Pushout pushout_rows_left pushout_rows_right.

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
