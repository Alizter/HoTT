(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import HProp HSet.
Require Import Spaces.Pos Spaces.Int.
Require Import HIT.Coeq.
Require Import Modalities.Modality Truncations.
Require Import Cubical.DPath.

Local Open Scope path_scope.

(** * Theorems about the circle [S1]. *)

Generalizable Variables X A B f g n.

(* ** Definition of the circle. *)

(** TODO: is this really a "naive" definition? *)
(** We define the circle as the coequalizer of two copies of the identity map of [Unit].  This is easily equivalent to the naive definition

<<<
Private Inductive S1 : Type0 :=
| base : S1
| loop : base = base.
>>>

but it allows us to apply the flattening lemma directly rather than having to pass across that equivalence.  *)

Definition S1 := @Coeq Unit Unit idmap idmap.
Definition base : S1 := coeq tt.
Definition loop : base = base := cglue tt.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : loop # b = b)
  : forall (x:S1), P x.
Proof.
  refine (Coeq_ind P (fun u => transport P (ap coeq (path_unit tt u)) b) _).
  intros []; exact l.
Defined.

Definition S1_ind_beta_loop
           (P : S1 -> Type) (b : P base) (l : loop # b = b)
: apD (S1_ind P b l) loop = l
  := Coeq_ind_beta_cglue P _ _ tt.

(** But we want to allow the user to forget that we've defined the circle in that way. *)
Arguments S1 : simpl never.
Arguments base : simpl never.
Arguments loop : simpl never.
Arguments S1_ind_beta_loop : simpl never.

(* ** The non-dependent eliminator *)

Definition S1_rec (P : Type) (b : P) (l : b = b)
  : S1 -> P
  := S1_ind (fun _ => P) b (transport_const _ _ @ l).

Definition S1_rec_beta_loop (P : Type) (b : P) (l : b = b)
  : ap (S1_rec P b l) loop = l.
Proof.
  unfold S1_rec.
  refine (cancelL (transport_const loop b) _ _ _).
  refine ((apD_const (S1_ind (fun _ => P) b _) loop)^ @ _).
  refine (S1_ind_beta_loop (fun _ => P) _ _).
Defined.

(* ** The loop space of the circle is the Integers. *)

Global Instance ispointed_S1 : IsPointed S1 := base.

(** We use encode-decode. *)

Section AssumeUnivalence.
Context `{Univalence}.

Definition S1_code : S1 -> Type
  := S1_rec Type Int (path_universe int_succ).

(* Transporting in the codes fibration is the successor autoequivalence. *)

Definition transport_S1_code_loop (z : Int)
  : transport S1_code loop z = int_succ z.
Proof.
  refine (transport_compose idmap S1_code loop z @ _).
  unfold S1_code; rewrite S1_rec_beta_loop.
  apply transport_path_universe.
Defined.

Definition transport_S1_code_loopV (z : Int)
  : transport S1_code loop^ z = int_pred z.
Proof.
  refine (transport_compose idmap S1_code loop^ z @ _).
  rewrite ap_V.
  unfold S1_code; rewrite S1_rec_beta_loop.
  rewrite <- (path_universe_V int_succ).
  apply transport_path_universe.
Defined.

(* Encode by transporting *)

Definition S1_encode (x:S1) : (base = x) -> S1_code x
  := fun p => p # zero.

(* Decode by iterating loop. *)

Definition S1_decode (x : S1) : S1_code x -> (base = x).
Proof.
  revert x; refine (S1_ind (fun x => S1_code x -> base = x) (loopexp loop) _).
  apply path_forall; intros z; simpl in z.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_paths_r loop _ @ _).
  rewrite transport_S1_code_loopV.
  destruct z as [n| |n].
  2: apply concat_Vp.
  { rewrite <- int_neg_pos_succ.
    unfold loopexp, loopexp_pos.
    rewrite pos_peano_ind_beta_pos_succ.
    apply concat_pV_p. }
  induction n as [|n nH] using pos_peano_ind.
  1: apply concat_1p.
  rewrite <- pos_add_1_r.
  change (pos (n + 1)%pos)
    with (int_succ (pos n)).
  rewrite int_pred_succ.
  cbn; rewrite pos_add_1_r.
  unfold loopexp_pos.
  rewrite pos_peano_ind_beta_pos_succ.
  reflexivity.
Defined.

(* The nontrivial part of the proof that decode and encode are equivalences is showing that decoding followed by encoding is the identity on the fibers over [base]. *)

Definition S1_encode_loopexp (z:Int)
  : S1_encode base (loopexp loop z) = z.
Proof.
  destruct z as [n | | n]; unfold S1_encode.
  - induction n using pos_peano_ind; simpl in *.
    + refine (moveR_transport_V _ loop _ _ _).
        by symmetry; apply transport_S1_code_loop.
    + unfold loopexp_pos.
      rewrite pos_peano_ind_beta_pos_succ.
      rewrite transport_pp.
      refine (moveR_transport_V _ loop _ _ _).
      refine (_ @ (transport_S1_code_loop _)^).
      refine (IHn @ _^).
      rewrite int_neg_pos_succ.
      by rewrite int_succ_pred.
  - reflexivity.
  - induction n using pos_peano_ind; simpl in *.
    + by apply transport_S1_code_loop.
    + unfold loopexp_pos.
      rewrite pos_peano_ind_beta_pos_succ.
      rewrite transport_pp.
      refine (moveR_transport_p _ loop _ _ _).
      refine (_ @ (transport_S1_code_loopV _)^).
      refine (IHn @ _^).
      rewrite <- pos_add_1_r.
      change (int_pred (int_succ (pos n)) = pos n).
      apply int_pred_succ.
Defined.

(* Now we put it together. *)

Definition S1_encode_isequiv (x:S1) : IsEquiv (S1_encode x).
Proof.
 refine (isequiv_adjointify (S1_encode x) (S1_decode x) _ _).
  (* Here we induct on [x:S1].  We just did the case when [x] is [base]. *)
  - refine (S1_ind (fun x => Sect (S1_decode x) (S1_encode x))
                   S1_encode_loopexp _ _).
    (* What remains is easy since [Int] is known to be a set. *)
    by apply path_forall; intros z; apply hset_path2.
  (* The other side is trivial by path induction. *)
  - intros []; reflexivity.
Defined.

Definition equiv_loopS1_int : (base = base) <~> Int
  := Build_Equiv _ _ (S1_encode base) (S1_encode_isequiv base).

(** ** Connectedness and truncatedness *)

(** The circle is 0-connected. *)
Global Instance isconnected_S1 : IsConnected 0 S1.
Proof.
  apply is0connected_merely_allpath.
  - exact (tr base).
  - simple refine (S1_ind _ _ _).
    + simple refine (S1_ind _ _ _).
      * exact (tr 1).
      * apply path_ishprop.
    + apply path_ishprop.
Defined.

(** It follows that the circle is a 1-type. *)
Global Instance istrunc_S1 : IsTrunc 1 S1.
Proof.
  intros x y.
  assert (p := merely_path_is0connected S1 base x).
  assert (q := merely_path_is0connected S1 base y).
  strip_truncations.
  destruct p, q.
  refine (trunc_equiv' (n := 0) Int equiv_loopS1_int^-1).
Defined.


(** ** Iteration of equivalences *)

(** If [P : S1 -> Type] is defined by a type [X] and an autoequivalence [f], then the image of [n:Int] regarded as in [base = base] is [iter_int f n]. *)
Definition S1_action_is_iter X (f : X <~> X) (n : Int) (x : X)
: transport (S1_rec Type X (path_universe f)) (equiv_loopS1_int^-1 n) x
  = int_iter f n x.
Proof.
  refine (_ @ loopexp_path_universe _ _ _).
  refine (transport_compose idmap _ _ _ @ _).
  refine (ap (fun p => transport idmap p x) _).
  unfold equiv_loopS1_int; cbn.
  unfold S1_decode; simpl.
  rewrite ap_loopexp.
  refine (ap (fun p => loopexp p n) _).
  apply S1_rec_beta_loop.
Qed.

End AssumeUnivalence.

(* An induction principle for S1 that produces a DPath *)
Definition S1_ind_dp (P : S1 -> Type) (b : P base)
  (bl : DPath P loop b b) (x : S1) : P x
  := S1_ind P b (dp_path_transport^-1 bl) x.

Definition S1_ind_dp_beta_loop (P : S1 -> Type) (b : P base)
  (bl : DPath P loop b b) : dp_apD (S1_ind_dp P b bl) loop = bl.
Proof.
  apply dp_apD_path_transport.
  exact (S1_ind_beta_loop _ _ _).
Defined.

(** Here is an alternative proof of the loop space of S1 being equivalent to the integers. *)
Module LoopS1Alternative.

  Section AssumeUnivalence.

    Context `{Univalence}.

    Local Open Scope positive_scope.

    (** The proof is somewhat similar to the encode-decode proof. In the encode-decode proof we defined maps between the fibers of the universal cover of the circle and paths from a given basepoint. The main work in the proof is showing that these maps are inverses of eachother hence there being an equivalence between the integers (fiber over the basepoint of the universal cover of the circle) and the loop space of the circle.

    Instead of showing that fibers of the universal cover and paths are equivalent, we show that the total spaces of these fibrations are equivalent. This can be done since both total spaces are contractible. Then via the "fundamental theorem of HoTT" we get that fiberwise equivalences are induced by equivalences of total spaces. *)

    (** First we define a winding function which takes an integer [z] and winds [loop] round [z] times. We use [pos_peano_ind] in order to do induction on positive and negative integers. Later we will need to reason about how this interacts with int_succ. *)
    Definition wind (z : Int) : base = base.
    Proof.
      refine (
        match z with
        | neg n => _
        | zero => _
        | pos n => _
        end).
      { (** Negative windings *)
        induction n as [|n IHn] using pos_peano_ind.
        { (** -1 case *)
          exact loop^. }
        (** < -1 case *)
        exact (IHn @ loop^). }
      { (** 0 case *)
        reflexivity. }
      (** Positive windings *)
      induction n as [|n IHn] using pos_peano_ind.
      { (** 1 case *)
        exact loop. }
      (** > 1 case *)
      exact (IHn @ loop).
    Defined.

    (** Concatenating a winding with [loop] increments the winding number. *)
    Definition wind_succ (z : Int)
      : wind z @ loop = wind (int_succ z).
    Proof.
      destruct z.
      { (** Negative windings *)
        (** We need to proceed by induction on the negative integer since we have to show that [loop @ loop^] reduces. *)
        induction p using pos_peano_ind.
        1: apply concat_Vp.
        refine (ap (fun x => x @ _) _ @ _).
        1: rapply pos_peano_ind_beta_pos_succ.
        refine (concat_pp_p _ _ _ @ _).
        refine (ap (fun x => _ @ x) _ @ _).
        1: apply concat_Vp.
        refine (concat_p1 _ @ _).
        refine (_ @ ap wind _^).
        2: apply int_pos_sub_succ_r.
        reflexivity. }
      (** 0 winding *)
      1: apply concat_1p.
      (** Positive winding *)
      (** This holds pretty much by definition. However [int_succ (pos p)] reduces to [pos (p + 1)] instead of [pos (pos_succ p)] so we have to rewrite. *) 
      symmetry; cbn.
      refine (ap _ _ @ _).
      1: apply pos_add_1_r.
      rapply pos_peano_ind_beta_pos_succ.
    Defined.

    (** Similarly, concatenating a winding with [loop^] decrements the winding number. The proof is essentially the same as before but backwards. *)
    Lemma wind_pred (z : Int)
      : wind z @ loop^ = wind (int_pred z).
    Proof.
      destruct z.
      { (** Negative windings *)
        symmetry; cbn.
        refine (ap _ _ @ _).
        1: apply pos_add_1_r.
        rapply pos_peano_ind_beta_pos_succ. }
      (** 0 winding *)
      1: apply concat_1p.
      (** Positive winding *)
      induction p using pos_peano_ind.
      1: apply concat_pV.
      refine (ap (fun x => x @ _) _ @ _).
      1: rapply pos_peano_ind_beta_pos_succ.
      refine (concat_pp_p _ _ _ @ _).
      refine (ap (fun x => _ @ x) _ @ _).
      1: apply concat_pV.
      refine (concat_p1 _ @ _).
      refine (_ @ ap wind (ap (int_pred o pos) _^ @ _)^).
      2: rapply pos_add_1_r.
      2: { change (pos (p + 1)) with (int_succ (pos p)).
        rapply int_pred_succ. }
      reflexivity.
    Defined.

    Lemma fiber_loop_action (x : S1_code base)
      : loop # x = int_succ x.
    Proof.
      unfold S1_code.
      refine (transport_idmap_ap _ _ _ _ _ _ @ _).
      rewrite S1_rec_beta_loop.
      apply transport_path_universe.
    Defined.

    Lemma fiber_opploop_action (x : S1_code base)
      : loop^ # x = int_pred x.
    Proof.
      unfold S1_code.
      refine (transport_idmap_ap _ _ _ _ _ _ @ _).
      rewrite ap_V.
      rewrite S1_rec_beta_loop.
      apply transport_path_universe_V.
    Defined.

  Lemma fiber_wind_action (z : Int) (x : S1_code base)
    : wind z # x = (x + z)%int.
  Proof.
    destruct z.
    { induction p using pos_peano_ind.
      1: apply fiber_opploop_action.
      simpl.
      rewrite pos_peano_ind_beta_pos_succ.
      rewrite transport_pp.
      rewrite IHp.
      rewrite fiber_opploop_action.
      rewrite <- pos_add_1_r.
      apply int_pred_add_r. }
    { symmetry.
      apply int_add_0_r. }
    induction p using pos_peano_ind.
    1: apply fiber_loop_action.
    simpl.
    rewrite pos_peano_ind_beta_pos_succ.
    rewrite transport_pp.
    rewrite IHp.
    rewrite fiber_loop_action.
    rewrite <- pos_add_1_r.
    symmetry.
    apply (int_add_succ_r x (pos p)).
  Defined.

  (** Now we show that the total space of the universal cover is contractible. *)
  Instance contr_total_S1_code : Contr (sigT S1_code).
  Proof.
    snrapply Build_Contr.
    { exists base.
      exact 0%int. }
    intros [x z].
(*     revert x z. *)
    { 
(*      intro z. *)
      srapply path_sigma.
      
      1: exact (wind z).
      simpl.
      apply fiber_wind_action. }
    funext x.
    rewrite transport_forall.
    simpl.
    srapply path_path_sigma.
    { unfold pr1_path.
    simpl.
    rapply path_ishprop.
      
  Admitted.



  (** The path fibration also has a contractible total space. *)
  Instance contr_total_paths_base : Contr (sigT (paths base)).
  Proof.
    apply contr_basedpaths_etashort.
  Defined.

  (** [S1_encode] is a map between fibers. Since both total spaces are contractible, the induced map between total spaces must be an equivalence. *)
  Instance isequiv_functor_sigma_idmap_S1_encode
    : IsEquiv (functor_sigma idmap S1_encode).
  Proof.
    apply isequiv_contr_contr.
  Defined.

  (** Hence [S1_encode] is an equivalence. *)
  Instance isequiv_S1_encode : forall x, IsEquiv (S1_encode x).
  Proof.
    intro x.
    apply isequiv_from_functor_sigma.
    apply isequiv_functor_sigma_idmap_S1_encode.
  Defined.

  (** Finally, we have an equivalence between the loop space of the circle and the integers. *)
  Theorem equiv_loopS1_int' : (base = base) <~> Int.
  Proof.
    apply (Build_Equiv _ _ (S1_encode base)).
    apply isequiv_S1_encode.
  Defined.



    (** The universal cover of the circle can be constructed with univalence. In HoTT a cover is just a family of hSets. The fibers of this family are all Int and [loop] gets mapped to the path constructed by univalcne from [int_succ]. *)
    Definition circle_cover : S1 -> Type
      := S1_rec Type Int (equiv_path_universe _ _ equiv_int_succ).



  

  End AssumeUnivalence.

End LoopS1Alternative.

