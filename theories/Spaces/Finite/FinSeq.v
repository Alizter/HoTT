Require Import Basics Types.
Require Import HSet DProp.
Require Import Spaces.Nat Spaces.Finite.Fin.
Require Import Spaces.Finite.FinInduction.

Local Unset Elimination Schemes.

Declare Scope fs_scope.
Local Open Scope fs_scope.

(** Finite-dimensional sequence or length-indexed lists. It is often also referred to as vector, but we call it finite sequence [FinSeq] to avoid confusion with vector from linear algebra. *)

Inductive FinSeq@{u} (A : Type@{u}) : nat -> Type@{u} :=
| fs_nil : FinSeq A 0
| fs_cons (n : nat) : A -> FinSeq A n -> FinSeq A n.+1
.

Scheme FinSeq_ind := Induction for FinSeq Sort Type.
Scheme FinSeq_rect := Induction for FinSeq Sort Type.
Scheme FinSeq_rec := Minimality for FinSeq Sort Type.

Arguments fs_nil {A}.
Arguments fs_cons {A n}.

(** List notations for sequences *)
(* Notation "[ ]" := fs_nil : fs_scope. *)
Infix "::" := fs_cons : fs_scope.
Notation "[ x ]" := (fs_cons x fs_nil) : fs_scope.
(** TODO: sometimes we get a parsing error, why is this? Probably some notation is reserved somewhere *)
Notation "[ x ; y ; .. ; z ]" := (fs_cons x (fs_cons y .. (fs_cons z fs_nil) ..))
  : fs_scope.

(** All finite sequences of zero length are equal. *)
Definition path_fs_nil {A : Type} (v : FinSeq A 0) : fs_nil = v :=
  match v with
  | fs_nil => idpath
  end.

(** So the type of finite sequences of zero length is contractible. *)
Global Instance contr_finseq_0 {A} : Contr (FinSeq A 0).
Proof.
  exists fs_nil.
  apply path_fs_nil.
Defined.

(** The head of a non-empty sequence *)
Definition fs_head {A} {n : nat} (v : FinSeq A n.+1) : A :=
  match v with
  | a :: v' => a
  end.

(** The tail of a non-empty sequence *)
Definition fs_tail {A} {n : nat} (v : FinSeq A n.+1) : FinSeq A n :=
  match v with
  | a :: v' => v'
  end.

(** A non-empty finite sequence is equal to [fs_cons] of head and tail. *)
Definition path_fs_eta {A : Type} {n : nat} (v : FinSeq A n.+1)
  : fs_cons (fs_head v) (fs_tail v) = v :=
  match v with
  |  a :: v' => idpath
  end.

Lemma equiv_fs_singleton {A : Type} : FinSeq A 1 <~> A.
Proof.
  snrapply (equiv_adjointify fs_head (fun x => [ x ])).
  1: reflexivity.
  intros x.
  refine (ap _ _ @ path_fs_eta x).
  apply path_contr.
Defined.

(** Induction for positive length lists *)
Definition FinSeq_indS {A} (P : forall n, FinSeq A n.+1 -> Type)
  (b : forall a, P 0 [ a ])
  (h : forall a n (v : FinSeq A n.+1), P n v -> P n.+1 (a :: v))
  (n : nat) (v : FinSeq A n.+1) : P n v.
Proof.
  refine (path_fs_eta _ # _).
  induction n.
  { rewrite (path_contr (fs_tail v) fs_nil).
    apply b. }
  apply h.
  rewrite <- (path_fs_eta (fs_tail v)).
  apply IHn.
Defined.

(** ** Operations on sequences *)

(** Concatenation of sequences *)
Fixpoint fs_concat {A n m} (v : FinSeq A n) (w : FinSeq A m) : FinSeq A (n + m) :=
  match v with
  | fs_nil => w
  | a :: v' => a :: (v' ++ w)
  end
where "a ++ b" := (fs_concat a b) : fs_scope.

(** Append an element to the end of a sequence. We can define this as concatenation but since the length would be "a + 1" we would have to rewrite this to be the successor all the time. *)
Fixpoint fs_append {A n} (v : FinSeq A n) (a : A) : FinSeq A n.+1 :=
  match v with
  | fs_nil => [ a ]
  | x :: v' => x :: fs_append v' a 
  end.

(** Reversing a sequence *)
(** Note that there are more efficient implementations for reversing lists using left-associative folds but it is unclear how to generalize these to dependent types for the time being. We also have to transport due to the index not computing correctly. *)
Fixpoint fs_reverse {A} {n : nat} (v : FinSeq A n) : FinSeq A n :=
  match v with
  | fs_nil => fs_nil
  | a :: v' => fs_append (fs_reverse v') a
  end.

Lemma path_fs_reverse_append {A n} (v : FinSeq A n) x
  : fs_reverse (fs_append v x) = x :: fs_reverse v.
Proof.
  induction v.
  1: reflexivity.
  cbn; by rewrite IHv.
Defined.

(** Reversing a sequence twice leaves it unchanges. *)
Lemma path_fs_reverse_reverse {A} {n : nat} (v : FinSeq A n)
  : fs_reverse (fs_reverse v) = v.
Proof.
  induction v.
  1: reflexivity.
  rewrite path_fs_reverse_append.
  f_ap.
Defined.

(** Append preserves tail *)
Lemma path_fs_tail_append {A n} (v : FinSeq A n.+1) (a : A)
  : fs_tail (fs_append v a) = fs_append (fs_tail v) a.
Proof.
  by refine (FinSeq_indS
    (fun n v => fs_tail (fs_append v a) = fs_append (fs_tail v) a) _ _ n v).
Defined.

(** Reversing a sequence is an equivalence. *)
Global Instance isequiv_fs_reverse {A} {n : nat} : IsEquiv (@fs_reverse A n)
  := isequiv_adjointify
      fs_reverse fs_reverse
      path_fs_reverse_reverse path_fs_reverse_reverse.

(** Last element of a sequence *)
Definition fs_last {A} {n : nat} (v : FinSeq A n.+1) : A
  := fs_head (fs_reverse v).

(** Initial segment of a sequence (excluding the last element) *)
Definition fs_init {A} {n : nat} (v : FinSeq A n.+1) : FinSeq A n
  := fs_reverse (fs_tail (fs_reverse v)).

(** We can derive an eta rule that decomposes sequences the other way *)
Lemma path_fs_eta' {A} {n : nat} (v : FinSeq A n.+1)
  : fs_append (fs_init v) (fs_last v) = v.
Proof.
  refine (FinSeq_indS (fun n v => fs_append (fs_init v) (fs_last v) = v) _ _ _ v).
  1: reflexivity.
  clear n v.
  intros a n v IH.
  unfold fs_init, fs_last.
  change (fs_append (fs_reverse ?v) ?x) with (fs_reverse (x :: v)).
  refine (ap fs_reverse _ @ eissect fs_reverse _).
  apply path_fs_eta.
Defined.

(** Initial segment of tail *)
Lemma path_fs_init_append {A n} (v : FinSeq A n) (a : A)
  : fs_init (fs_append v a) = v.
Proof.
  induction v.
  1: reflexivity.
  unfold fs_init.
  rewrite 2 path_fs_reverse_append.
  f_ap.
  apply path_fs_reverse_reverse.
Defined.

(** ** Equivalence of [FinSeq] and [Fin n -> A] *)

(** Our definition of FinSeq is a standard list definition found in most programming languages. Our definition of Fin is however a bit different. In Fin, the top most element is the last element whereas in FinSeq the top most element is the first. We therefore need an induction principle that breaks up our sequences from the other end. *)

Definition FinSeq_ind' {A : Type}
  (P : forall n : nat, FinSeq A n -> Type) (h : P 0 fs_nil)
  (t : forall n a (v : FinSeq A n), P n v -> P n.+1 (fs_append v a))
  : forall (n : nat) (v : FinSeq A n), P n v.
Proof.
  intros n v.
  refine (eissect fs_reverse v # _).
  apply (FinSeq_ind _ (fun n v => P n (fs_reverse v))).
  1: assumption.
  clear n v.
  intros n a f p.
  refine (path_fs_eta' _ # _).
  apply t.
  cbn.
  rewrite path_fs_init_append.
  apply p.
Defined.

(** Projection of nth element from a sequence *)
Definition fs_proj {A} {n : nat} (v : FinSeq A n) : Fin n -> A.
Proof.
  revert n v.
  refine (FinSeq_ind' _ _ _).
  1: exact Empty_rec.
  intros n a v f [x | ].
  + exact (f x).
  + exact a.
Defined.

(** Here is a convenient projector for non-empty sequences. Note that if the index is out of range it will wrap around. *)
Definition fs_proj' {A} {n : nat} (v : FinSeq A n.+1) (n : nat) : A
  := fs_proj v (fin_nat n).

Definition fs_from_fin {A} n (F : Fin n -> A) : FinSeq A n.
Proof.
  induction n.
  1: exact fs_nil.
  exact (fs_append (IHn (F o fin_incl)) (F fin_last)).
Defined.

Definition fs_from_fin' {A} n (F : forall k, k < n -> A)
  : FinSeq A n.
Proof.
  apply fs_from_fin.
  intros t.
  srapply F.
  2: by rapply FinNat.is_bounded_fin_to_nat.
Defined.

(* Theorem equiv_fs_fin `{Funext} {A n} : FinSeq A n <~> (Fin n -> A).
Proof.
  snrapply equiv_adjointify.
  1: exact fs_proj.
  { intros f.
    apply fs_from_fin.
    intros k p.
  
  intros f.
    induction n.
    1: exact fs_nil.
    exact (fs_append (IHn (f o fin_incl)) (f fin_last)). }
  - hnf.
    intros x.
    induction n.
    { apply path_forall.
      intros [ ]. }
    simpl.
    
 *)    

  (* 

(* Definition FinSeq@{u} (n : nat) (A : Type@{u}) : Type@{u} := Fin n -> A. *)

(** The empty finite sequence. *)

(* Definition fsnil {A : Type} : FinSeq 0 A := Empty_rec. *)



(** Add an element in the end of a finite sequence, [fscons'] and [fscons]. *)

Definition fscons' {A : Type} (n : nat) (a : A) (v : FinSeq (pred n) A)
  : FinSeq n A
  := fun i =>  fin_rec (fun n => FinSeq (pred n) A -> A)
                       (fun _ _ => a) (fun n' i _ v => v i) i v.

Definition fscons {A : Type} {n : nat} : A -> FinSeq n A -> FinSeq n.+1 A
  := fscons' n.+1.

(** Take the first element of a non-empty finite sequence,
    [fshead'] and [fshead]. *)

Definition fshead' {A} (n : nat) : n > 0 -> FinSeq n A -> A
  := match n with
     | 0 => fun N _ => Empty_rec N
     | n'.+1 => fun _ v => v fin_zero
     end.

Definition fshead {A} {n : nat} : FinSeq n.+1 A -> A := fshead' n.+1 tt.

Definition compute_fshead' {A} n (N : n > 0) (a : A) (v : FinSeq (pred n) A)
  : fshead' n N (fscons' n a v) = a.
Proof.
  destruct n; [elim N|].
  exact (apD10 (compute_fin_rec_fin_zero _ _ _ _) v).
Defined.

Definition compute_fshead {A} {n} (a : A) (v : FinSeq n A)
  : fshead (fscons a v) = a.
Proof.
  apply compute_fshead'.
Defined.

(** If the sequence is non-empty, then remove the first element. *)

Definition fstail' {A} (n : nat) : FinSeq n A -> FinSeq (pred n) A
  := match n with
     | 0 => fun _ => Empty_rec
     | n'.+1 => fun v i => v (fsucc i)
     end.

(** Remove the first element from a non-empty sequence. *)

Definition fstail {A} {n : nat} : FinSeq n.+1 A -> FinSeq n A := fstail' n.+1.

Definition compute_fstail' {A} n (a : A) (v : FinSeq (pred n) A)
  : fstail' n (fscons' n a v) == v.
Proof.
  intro i.
  destruct n; [elim i|].
  exact (apD10 (compute_fin_rec_fsucc _ _ _ _) v).
Defined.

Definition compute_fstail `{Funext} {A} {n} (a : A) (v : FinSeq n A)
  : fstail (fscons a v) = v.
Proof.
  funext i.
  apply compute_fstail'.
Defined.

(** A non-empty finite sequence is equal to [fscons] of head and tail,
    [path_expand_fscons'] and [path_expand_fscons]. *)

Lemma path_expand_fscons' {A : Type} (n : nat)
  (i : Fin n) (N : n > 0) (v : FinSeq n A)
  : fscons' n (fshead' n N v) (fstail' n v) i = v i.
Proof.
  induction i using fin_ind.
  - apply compute_fshead.
  - apply (compute_fstail' n.+1 (fshead v) (fstail v)).
Defined.

Lemma path_expand_fscons `{Funext} {A} {n} (v : FinSeq n.+1 A)
  : fscons (fshead v) (fstail v) = v.
Proof.
  funext i.
  apply path_expand_fscons'.
Defined.

(** The following [path_fscons'] and [path_fscons] gives a way to construct
    a path between [fscons] finite sequences. They cooperate nicely with
    [path_expand_fscons'] and [path_expand_fscons]. *)

Definition path_fscons' {A} n {a1 a2 : A} {v1 v2 : FinSeq (pred n) A}
  (p : a1 = a2) (q : forall i, v1 i = v2 i) (i : Fin n)
  : fscons' n a1 v1 i = fscons' n a2 v2 i.
Proof.
  induction i using fin_ind.
  - exact (compute_fshead _ _ @ p @ (compute_fshead _ _)^).
  - refine (_ @ (compute_fstail' n.+1 a2 v2 i)^).
    exact (compute_fstail' n.+1 a1 v1 i @ q i).
Defined.

Definition compute_path_fscons' {A} (n : nat)
    (a : A) (v : FinSeq (pred n) A) (i : Fin n)
    : path_fscons' n (idpath a) (fun j => idpath (v j)) i = idpath.
Proof.
  induction i using fin_ind; unfold path_fscons'.
  - rewrite compute_fin_ind_fin_zero.
    refine (ap (fun p => p @ _) (concat_p1 _) @ _).
    apply concat_pV.
  - rewrite compute_fin_ind_fsucc.
    refine (ap (fun p => p @ _) (concat_p1 _) @ _).
    apply concat_pV.
Qed.

Definition path_fscons `{Funext} {A} {n} {a1 a2 : A} (p : a1 = a2)
  {v1 v2 : FinSeq n A} (q : v1 = v2)
  : fscons a1 v1 = fscons a2 v2.
Proof.
  funext i. apply path_fscons'.
  - assumption.
  - intro j. exact (apD10 q j).
Defined.

Lemma compute_path_fscons `{Funext} {A} {n} (a : A) (v : FinSeq n A)
  : path_fscons (idpath a) (idpath v) = idpath.
Proof.
  refine (ap (path_forall _ _) _ @ eta_path_forall _ _ _).
  funext i. exact (compute_path_fscons' n.+1 a v i).
Defined.

(** The lemmas [path_expand_fscons_fscons'] and [path_expand_fscons_fscons]
    identify [path_expand_fscons'] with [path_fscons'] and
    [path_expand_fscons] with [path_fscons]. *)

Lemma path_expand_fscons_fscons' {A : Type} (n : nat)
  (N : n > 0) (a : A) (v : FinSeq (pred n) A) (i : Fin n)
  : path_expand_fscons' n i N (fscons' n a v) =
    path_fscons' n (compute_fshead' n N a v) (compute_fstail' n a v) i.
Proof.
  induction i using fin_ind; unfold path_fscons', path_expand_fscons'.
  - do 2 rewrite compute_fin_ind_fin_zero.
    refine (_ @ concat_p_pp _ _ _).
    refine (_ @ (ap (fun p => _ @ p) (concat_pV _))^).
    exact (concat_p1 _)^.
  - do 2 rewrite compute_fin_ind_fsucc.
    refine (_ @ concat_p_pp _ _ _).
    refine (_ @ (ap (fun p => _ @ p) (concat_pV _))^).
    exact (concat_p1 _)^.
Qed.

Lemma path_expand_fscons_fscons `{Funext}
  {A : Type} {n : nat} (a : A) (v : FinSeq n A)
  : path_expand_fscons (fscons a v) =
    path_fscons (compute_fshead a v) (compute_fstail a v).
Proof.
  refine (ap (path_forall _ _) _).
  funext i.
  pose (p := eisretr apD10 (compute_fstail' n.+1 a v)).
  refine (_ @ (ap (fun f => _ f i) p)^).
  exact (path_expand_fscons_fscons' n.+1 tt a v i).
Defined.

(** The induction principle for finite sequence, [finseq_ind].
    Note that it uses funext and does not compute. *)

Lemma finseq_ind `{Funext} {A : Type} (P : forall n, FinSeq n A -> Type)
  (z : P 0 fsnil) (s : forall n a (v : FinSeq n A), P n v -> P n.+1 (fscons a v))
  {n : nat} (v : FinSeq n A)
  : P n v.
Proof.
  induction n.
  - exact (transport (P 0) (path_fsnil v) z).
  - refine (transport (P n.+1) (path_expand_fscons v) _).
    apply s. apply IHn.
Defined.

Lemma compute_finseq_ind_fsnil `{Funext} {A : Type}
  (P : forall n, FinSeq n A -> Type) (z : P 0 fsnil)
  (s : forall (n : nat) (a : A) (v : FinSeq n A), P n v -> P n.+1 (fscons a v))
  : finseq_ind P z s fsnil = z.
Proof.
  exact (ap (fun x => _ x z) (hset_path2 1 (path_fsnil fsnil)))^.
Defined.

Lemma compute_finseq_ind_fscons `{Funext} {A : Type}
  (P : forall n, FinSeq n A -> Type) (z : P 0 fsnil)
  (s : forall (n : nat) (a : A) (v : FinSeq n A), P n v -> P n.+1 (fscons a v))
  {n : nat} (a : A) (v : FinSeq n A)
  : finseq_ind P z s (fscons a v) = s n a v (finseq_ind P z s v).
Proof.
  simpl.
  induction (path_expand_fscons_fscons a v)^.
  set (p1 := compute_fshead a v).
  set (p2 := compute_fstail a v).
  induction p1, p2.
  exact (ap (fun p => transport _ p _) (compute_path_fscons _ _)).
Defined. *)

