(** * Theorems about path spaces *)

Require Import Basics.Overture Basics.Equivalences Basics.PathGroupoids Basics.Tactics.

Local Open Scope path_scope.

Generalizable Variables A B f x y z.

(** ** Path spaces *)

(** The path spaces of a path space are not, of course, determined; they are just the higher-dimensional structure of the original space. *)

(** ** Transporting in path spaces *)

(* There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

- `l` means the left endpoint varies
- `r` means the right endpoint varies
- `F` means application of a function to that (varying) endpoint.

Examples of usage can be found in test/Tactics/transport_paths.v *)

(** *** 0 functions *)

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = p^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

(** *** 1 function *)

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Flr {A : Type} {f : A -> A} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = x1)
  : transport (fun x => f x = x) p q = (ap f p)^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_lFr {A : Type} {f : A -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = f x1)
  : transport (fun x => x = f x) p q = p^ @ q @ (ap f p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p. symmetry; apply concat_p1.
Defined.

(** *** 2 functions *)

Definition transport_paths_FFl {A B C : Type} {f : A -> B} {g : B -> C}
  {x1 x2 : A} {y : C} (p : x1 = x2) (q : g (f x1) = y)
  : transport (fun x => g (f x) = y) p q = (ap g (ap f p))^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = (ap g (ap f p))^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFr_D {A : Type} {B : A -> Type}
  {f g : forall a, B a} {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1)
: transport (fun x => f x = g x) p q
  = (apD f p)^ @ ap (transport B p) q @ (apD g p).
Proof.
  destruct p; simpl.
  exact ((ap_idmap _)^ @ (concat_1p _)^ @ (concat_p1 _)^).
Defined.

Definition transport_paths_lFFr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  : transport (fun x => x = g (f x)) p q = p^ @ q @ (ap g (ap f p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FFr {A B C : Type} {f : A -> B} {g : B -> C}
  {x1 x2 : A} {y : C} (p : x1 = x2) (q : y = g (f x1))
  : transport (fun x => y = g (f x)) p q = q @ (ap g (ap f p)).
Proof.
  destruct p. symmetry; apply concat_p1.
Defined.

(** *** 3 functions *)

Definition transport_paths_FFFl {A B C D : Type}
  {f : A -> B} {g : B -> C} {h : C -> D} {x1 x2 : A} {y : D}
  (p : x1 = x2) (q : h (g (f x1)) = y)
  : transport (fun x => h (g (f x)) = y) p q = (ap h (ap g (ap f p)))^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_FFFlr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : C -> A} {x1 x2 : A}
  (p : x1 = x2) (q : h (g (f x1)) = x1)
  : transport (fun x => h (g (f x)) = x) p q = (ap h (ap g (ap f p)))^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FFlFr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : A -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = h x1)
  : transport (fun x => g (f x) = h x) p q = (ap g (ap f p))^ @ q @ (ap h p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFFr {A B C : Type}
  {f : A -> C} {g : B -> C} {h : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g (h x1))
  : transport (fun x => f x = g (h x)) p q = (ap f p)^ @ q @ (ap g (ap h p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_lFFFr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : C -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = h (g (f x1)))
  : transport (fun x => x = h (g (f x))) p q = p^ @ q @ ap h (ap g (ap f p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FFFr {A B C D : Type}
  {f : A -> B} {g : B -> C} {h : C -> D} {x1 x2 : A} {y : D}
  (p : x1 = x2) (q : y = h (g (f x1)))
  : transport (fun x => y = h (g (f x))) p q = q @ ap h (ap g (ap f p)).
Proof.
  destruct p. symmetry; apply concat_p1.
Defined.

(** *** 4 functions *)

Definition transport_paths_FFFlFr {A B C D : Type}
  {f : A -> B} {g : B -> C} {h : C -> D} {k : A -> D} {x1 x2 : A}
  (p : x1 = x2) (q : h (g (f x1)) = k x1)
  : transport (fun x => h (g (f x)) = k x) p q = (ap h (ap g (ap f p)))^ @ q @ (ap k p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FFlFFr {A B B' C : Type}
  {f : A -> B} {f' : A -> B'} {g : B -> C} {g' : B' -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = g' (f' x1))
  : transport (fun x => g (f x) = g' (f' x)) p q = (ap g (ap f p))^ @ q @ (ap g' (ap f' p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

(** Transport an associator assembled from a comparison with right translation. Combining the translation path with the path in the last input removes the two separate endpoint corrections. *)
Definition transport_associator_normal_form
  {A : Type} (mu : A -> A -> A)
  {z0 z1 : A} (p : z0 = z1) (r : A -> A)
  (rho : forall v, mu v z0 = r v)
  (E : forall x y, mu x (r y) = r (mu x y))
  (x y : A)
  : let eta := fun v => (rho v)^ @ ap (mu v) p in
    transport (fun z => mu (mu x y) z = mu x (mu y z)) p
      ((rho (mu x y) @ (E x y)^) @ ap (mu x) (rho y)^)
    = ((eta (mu x y))^ @ (E x y)^) @ ap (mu x) (eta y).
Proof.
  destruct p; cbn.
  rewrite !concat_p1, inv_V.
  reflexivity.
Defined.

(** The above lemmas have some common rearrangements that are useful. Since these all follow the same pattern, we introduce a tactic to apply it. *)

(** The most common rearrangement after applying the [transport_paths_] lemmas on the [lhs]. *)
Definition moveR_Vp_p_inv {A : Type} {w x y z : A}
  (p : x = w) (q : x = y) (r : y = z) (s : w = z)
  (h : p @ s = q @ r)
  : p^ @ q @ r = s.
Proof.
  lhs napply concat_pp_p.
  apply moveR_Vp, h^.
Defined.

Tactic Notation "transport_paths" uconstr(lemma) :=
  lhs napply lemma; apply moveR_Vp_p_inv.

Tactic Notation "transport_paths'" uconstr(lemma) :=
  lhs napply lemma; apply moveR_Vp.

Tactic Notation "transport_paths" "l" := lhs napply transport_paths_l.
Tactic Notation "transport_paths" "lr" := transport_paths transport_paths_lr.
Tactic Notation "transport_paths" "r" := lhs napply transport_paths_r.

Tactic Notation "transport_paths" "Fl" := transport_paths' transport_paths_Fl.
Tactic Notation "transport_paths" "Flr" := transport_paths transport_paths_Flr.
Tactic Notation "transport_paths" "lFr" := transport_paths transport_paths_lFr.
Tactic Notation "transport_paths" "Fr" := lhs napply transport_paths_Fr.

Tactic Notation "transport_paths" "FFl" := transport_paths' transport_paths_FFl.
Tactic Notation "transport_paths" "FFlr" := transport_paths transport_paths_FFlr.
Tactic Notation "transport_paths" "FlFr" := transport_paths transport_paths_FlFr.
Tactic Notation "transport_paths" "FlFr_D" := transport_paths transport_paths_FlFr_D.
Tactic Notation "transport_paths" "lFFr" := transport_paths transport_paths_lFFr.
Tactic Notation "transport_paths" "FFr" := lhs napply transport_paths_FFr.

Tactic Notation "transport_paths" "FFFl" := transport_paths' transport_paths_FFFl.
Tactic Notation "transport_paths" "FFFlr" := transport_paths transport_paths_FFFlr.
Tactic Notation "transport_paths" "FFlFr" := transport_paths transport_paths_FFlFr.
Tactic Notation "transport_paths" "FlFFr" := transport_paths transport_paths_FlFFr.
Tactic Notation "transport_paths" "lFFFr" := transport_paths transport_paths_lFFFr.
(** Coq is unable to unify the 3 functions appearing here. We therefore help it a bit instead. *)
(* Tactic Notation "transport_paths" "FFFr" := lhs napply transport_paths_FFFr. *)
Tactic Notation "transport_paths" "FFFr" :=
  match goal with
  | [ |- transport (fun x => ?y = ?h (?g (?f x))) ?p ?q = ?r ]
    => lhs exact (transport_paths_FFFr (f:=f) (g:=g) (h:=h) p q)
  end.

Tactic Notation "transport_paths" "FFFlFr" := transport_paths transport_paths_FFFlFr.
Tactic Notation "transport_paths" "FFlFFr" := transport_paths transport_paths_FFlFFr.

Definition transport011_paths {A B X} (f : A -> X) (g : B -> X)
  {a1 a2 : A} {b1 b2 : B} (p : a1 = a2) (q : b1 = b2)
  (r : f a1 = g b1)
  : transport011 (fun a b => f a = g b) p q r = (ap f p)^ @ r @ ap g q.
Proof.
  destruct p, q; cbn.
  symmetry.
  lhs napply concat_p1.
  apply concat_1p.
Defined.

(** ** Transporting in 2-path types *)

Definition transport_paths2 {A : Type} {x y : A}
           (p : x = y) (q : idpath x = idpath x)
: transport (fun a => idpath a = idpath a) p q
  =  (concat_Vp p)^
    @ whiskerL p^ ((concat_1p p)^ @ whiskerR q p @ concat_1p p)
    @ concat_Vp p.
Proof.
  destruct p. simpl.
  refine (_ @ (concat_p1 _)^).
  refine (_ @ (concat_1p _)^).
  (** The tricky thing here is getting a sufficiently general statement that we can prove it by path induction. *)
  assert (H : forall (p : x = x) (q : 1 = p),
                (q @ (concat_p1 p)^) @ (concat_1p (p @ 1))^
                = whiskerL (idpath x) (idpath 1 @ whiskerR q 1 @ idpath (p @ 1))).
  { intros p' q'. destruct q'. reflexivity. }
  transitivity (q @ (concat_p1 1)^ @ (concat_1p 1)^).
  { simpl; exact ((concat_p1 _)^ @ (concat_p1 _)^). }
  exact (H 1 q).
Defined.

(** ** Functorial action *)

(** 'functor_path' is called [ap]. *)

(** ** Equivalences between path spaces *)

(** [isequiv_ap] and [equiv_ap] are in Equivalences.v  *)

(** ** Path operations are equivalences *)

Instance isequiv_path_inverse {A : Type} (x y : A)
  : IsEquiv (@inverse A x y) | 0.
Proof.
  refine (Build_IsEquiv _ _ _ (@inverse A y x)
                       (@inv_V A y x) (@inv_V A x y) _).
  intros p; destruct p; reflexivity.
Defined.

Definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) <~> (y = x)
  := Build_Equiv _ _ (@inverse A x y) _.

Instance isequiv_concat_l {A : Type} `(p : x = y:>A) (z : A)
  : IsEquiv (concat_l (z:=z) p) | 0.
Proof.
  refine (Build_IsEquiv _ _ _ (concat p^)
                       (concat_p_Vp p) (concat_V_pp p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) <~> (x = z)
  := Build_Equiv _ _ (concat_l p) _.

Instance isequiv_concat_r {A : Type} `(p : y = z) (x : A)
  : IsEquiv (concat_r (x:=x) p) | 0.
Proof.
  refine (Build_IsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
           (fun q => concat_pV_p q p) (fun q => concat_pp_V q p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) <~> (x = z)
  := Build_Equiv _ _ (concat_r p) _.

Instance isequiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : IsEquiv (concat_lr p q) | 0
  := isequiv_compose (concat_l p) (concat_r q).

Definition equiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : (x = y) <~> (x' = y')
  := Build_Equiv _ _ (concat_lr p q) _.

Definition equiv_p1_1q {A : Type} {x y : A} {p q : x = y}
  : p = q <~> p @ 1 = 1 @ q
  := equiv_concat_lr (concat_p1 p) (concat_1p q)^.

Definition equiv_1p_q1 {A : Type} {x y : A} {p q : x = y}
  : p = q <~> 1 @ p = q @ 1
  := equiv_concat_lr (concat_1p p) (concat_p1 q)^.

(** Zigzag naturality respects the unit-boundary encoding of comparisons. *)
Definition concat_pV_natural_computation {A : Type} {x y z : A}
  {p p' r : x = z} {q q' s : y = z}
  (hp : p = r) (hp' : p' = r) (hq : q = s) (hq' : q' = s)
  : concat_pV_natural 1 1 1
      (equiv_p1_1q (hp @ hp'^)) (equiv_p1_1q (hq @ hq'^))
    = equiv_p1_1q ((hp @@ inverse2 hq) @ (hp' @@ inverse2 hq')^).
Proof.
  destruct hp, hp', hq, hq', p', q'; reflexivity.
Defined.

Definition equiv_p1_1q_concat {A : Type} {x y : A}
  {p p' q q' r : x = y}
  (u : p = p') (v : p' = r) (w : q' = r) (z : q = q')
  : ((u @@ 1) @ equiv_p1_1q (v @ w^)) @ (1 @@ z)^
    = equiv_p1_1q ((u @ v) @ (z @ w)^).
Proof.
  destruct u, v, w, z, q; reflexivity.
Defined.

Instance isequiv_whiskerL {A} {x y z : A} (p : x = y) {q r : y = z}
: IsEquiv (@whiskerL A x y z p q r).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply cancelL.
  - intros k. unfold cancelL.
    rewrite !whiskerL_pp.
    refine ((_ @@ 1 @@ _) @ whiskerL_pVL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
  - intros k. unfold cancelL.
    refine ((_ @@ 1 @@ _) @ whiskerL_VpL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
Defined.

Definition equiv_whiskerL {A} {x y z : A} (p : x = y) (q r : y = z)
: (q = r) <~> (p @ q = p @ r)
  := Build_Equiv _ _ (whiskerL p) _.

Definition equiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) <~> (q = r)
  := equiv_inverse (equiv_whiskerL p q r).

Definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : IsEquiv (cancelL p q r).
Proof.
  change (IsEquiv (equiv_cancelL p q r)); exact _.
Defined.

Instance isequiv_whiskerR {A} {x y z : A} {p q : x = y} (r : y = z)
: IsEquiv (fun h => @whiskerR A x y z p q h r).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply cancelR.
  - intros k. unfold cancelR.
    rewrite !whiskerR_pp.
    refine ((_ @@ 1 @@ _) @ whiskerR_VpR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
  - intros k. unfold cancelR.
    refine ((_ @@ 1 @@ _) @ whiskerR_pVR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
Defined.

Definition equiv_whiskerR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p = q) <~> (p @ r = q @ r)
  := Build_Equiv _ _ (fun h => whiskerR h r) _.

Definition equiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) <~> (p = q)
  := equiv_inverse (equiv_whiskerR p q r).

Definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : IsEquiv (cancelR p q r).
Proof.
  change (IsEquiv (equiv_cancelR p q r)); exact _.
Defined.

(** We can use these to build up more complicated equivalences.

In particular, all of the [move] family are equivalences.

(Note: currently, some but not all of these [isequiv_] lemmas have corresponding [equiv_] lemmas.  Also, they do *not* currently contain the computational content that e.g. the inverse of [moveR_Mp] is [moveL_Vp]; perhaps it would be useful if they did? *)

Instance isequiv_moveR_Mp
 {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_Mp p q r).
Proof.
  destruct r; apply isequiv_concat_lr.
  (* [isequiv_concat_lr] is also found by typeclass search, but this is clearer to the reader. *)
Defined.

Definition equiv_moveR_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (p = r^ @ q) <~> (r @ p = q)
:= Build_Equiv _ _ (moveR_Mp p q r) _.

Instance isequiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_pM p q r).
Proof.
  destruct p; apply isequiv_concat_lr.
Defined.

Definition equiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r = q @ p^) <~> (r @ p = q)
:= Build_Equiv _ _ (moveR_pM p q r) _.

Instance isequiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveR_Vp p q r).
Proof.
  destruct r; apply isequiv_concat_lr.
Defined.

Definition equiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: (p = r @ q) <~> (r^ @ p = q)
:= Build_Equiv _ _ (moveR_Vp p q r) _.

(** The path-algebra conversion used by [transport_paths FlFr] is an equivalence. Its forward map retains the same transport and reassociation witnesses as that tactic. *)
Definition equiv_naturality_transport {A B : Type} (f g : A -> B)
  {x y : A} (p : x = y) (u : f x = g x) (v : f y = g y)
  : (ap f p @ v = u @ ap g p)
      <~> (transport (fun z => f z = g z) p u = v)
  := equiv_concat_l (transport_paths_FlFr p u) v
       oE equiv_concat_l (concat_pp_p (ap f p)^ u (ap g p)) v
       oE equiv_moveR_Vp (u @ ap g p) v (ap f p)
       oE equiv_path_inverse _ _.

Definition equiv_naturality_transport_apD {A B : Type}
  {f g : A -> B} (h : f == g) {x y : A} (p : x = y)
  : equiv_naturality_transport f g p (h x) (h y) (concat_Ap h p)
    = apD h p.
Proof.
  destruct p; cbn.
  generalize (h x).
  generalize (g x).
  intros z q; destruct q.
  reflexivity.
Defined.

(** Naturality of a comparison between two homotopies is the dependent transport equation for that comparison. *)
Definition equiv_naturality_transport2 {A B : Type} {f g : A -> B}
  (h k : f == g) {x y : A} (p : x = y)
  (u : h x = k x) (v : h y = k y)
  : (concat_Ap h p @ (u @@ 1) = (1 @@ v) @ concat_Ap k p)
    <~> (transport (fun z => h z = k z) p u = v).
Proof.
  destruct p; cbn.
  revert u v.
  generalize (k x).
  generalize (h x).
  generalize (g x).
  intros w a b u v.
  destruct a, u; cbn.
  exact (equiv_concat_r (concat_p1 (1 @@ v) @ whiskerL_1p_1 v) 1).
Defined.

(** A cube of naturality squares is the dependent transport equation for a square of homotopies. The four homotopies and the two selected endpoint squares are arbitrary. *)
Definition transport_naturality_square {A B : Type}
  {f0 f1 g0 g1 : A -> B}
  (u : f0 == f1) (v : g0 == g1)
  (h : f0 == g0) (k : f1 == g1)
  {x y : A} (p : x = y)
  (q : u x @ k x = h x @ v x)
  (r : u y @ k y = h y @ v y)
  (c : concat_natural (ap f0 p) (ap f1 p) (ap g1 p)
      (u x) (u y) (k x) (k y) (concat_Ap u p) (concat_Ap k p)
      @ (q @@ 1)
    = (1 @@ r) @ concat_natural (ap f0 p) (ap g0 p) (ap g1 p)
      (h x) (h y) (v x) (v y) (concat_Ap h p) (concat_Ap v p))
  : transport (fun z => u z @ k z = h z @ v z) p q = r.
Proof.
  nrefine (equiv_naturality_transport2
    (fun z => u z @ k z) (fun z => h z @ v z) p q r _).
  lhs napply (concat_Ap_concat u k p @@ 1).
  rhs napply (1 @@ concat_Ap_concat h v p).
  exact c.
Defined.

(** Fill the remaining face of a cube by pasting the five specified faces. All edges are inferred from the face types; no equality of parallel fillers is used. *)
Definition naturality_square_filler {T : Type}
  {x0 x1 x2 x3 y0 y1 y2 y3 : T}
  {p0 : x0 = y0} {p1 : x1 = y1} {p2 : x2 = y2} {p3 : x3 = y3}
  {u0 : x0 = x1} {u1 : y0 = y1} {v0 : x2 = x3} {v1 : y2 = y3}
  {h0 : x0 = x2} {h1 : y0 = y2} {k0 : x1 = x3} {k1 : y1 = y3}
  (nu : p0 @ u1 = u0 @ p1) (nv : p2 @ v1 = v0 @ p3)
  (nh : p0 @ h1 = h0 @ p2) (nk : p1 @ k1 = k0 @ p3)
  (s : u0 @ k0 = h0 @ v0) : u1 @ k1 = h1 @ v1
  := cancelL p0 _ _
    ((concat_natural p0 p1 p3 u0 u1 k0 k1 nu nk @ (s @@ 1))
      @ (concat_natural p0 p2 p3 h0 h1 v0 v1 nh nv)^).

(** Transport of a square is this explicit five-face pasting. In particular, its four side faces are the actual naturality comparisons of the four homotopies. *)
Definition transport_naturality_square_compute {A T : Type}
  {f0 f1 g0 g1 : A -> T}
  (u : f0 == f1) (v : g0 == g1)
  (h : f0 == g0) (k : f1 == g1)
  {x y : A} (p : x = y) (s : u x @ k x = h x @ v x)
  : transport (fun z => u z @ k z = h z @ v z) p s
    = naturality_square_filler (concat_Ap u p) (concat_Ap v p)
        (concat_Ap h p) (concat_Ap k p) s.
Proof.
  unfold naturality_square_filler.
  rhs_V napply (ap (fun a => cancelL (ap f0 p) _ _
    ((a @ (s @@ 1)) @ _)) (concat_Ap_concat u k p)).
  rhs_V napply (ap (fun b => cancelL (ap f0 p) _ _
    ((_ @ (s @@ 1)) @ b^)) (concat_Ap_concat h v p)).
  destruct p; cbn.
  revert s.
  generalize (u x @ k x), (h x @ v x).
  generalize (g1 x).
  intros z r t s; destruct r, s; reflexivity.
Defined.

(** Adjust the two endpoint edges of a naturality square while retaining its center. *)
Definition adjusted_naturality
  {X T : Type} {f g : X -> T} {x0 x1 : X} (r : x0 = x1)
  (A : f == g) (B0 : f x0 = g x0) (B1 : f x1 = g x1)
  (l : A x0 = B0) (k : A x1 = B1)
  := (ap (fun e => ap f r @ e) k)^ @
      (concat_Ap A r @ ap (fun e => e @ ap g r) l).

(** If both endpoint adjustments come from one pointwise comparison, the adjusted square is naturality of the target homotopy. *)
Definition adjusted_naturality_homotopic
  {X T : Type} {f g : X -> T} {x0 x1 : X} (r : x0 = x1)
  (A B : f == g) (q : forall x, A x = B x)
  : adjusted_naturality r A (B x0) (B x1) (q x0) (q x1)
    = concat_Ap B r.
Proof.
  napply moveR_Vp.
  exact (concat_Ap_homotopic A B q r).
Defined.

(** A comparison of squares descends through four chosen endpoint identifications only when the endpoint comparisons are their specified ratios. *)
Definition adjusted_square_comparison
  {P Q T : Type} (L : P -> T) (R : Q -> T)
  {a0 b0 z0 : P} {a1 b1 z1 : Q}
  (nA : R a1 = L a0) (nB : R b1 = L b0)
  (lA : a0 = z0) (kA : a1 = z1)
  (lB : b0 = z0) (kB : b1 = z1)
  (q0 : a0 = b0) (q1 : a1 = b1)
  (ql : q0 = lA @ lB^) (qk : q1 = kA @ kB^)
  (n : nA @ ap L q0 = ap R q1 @ nB)
  : (ap R kA)^ @ (nA @ ap L lA)
    = (ap R kB)^ @ (nB @ ap L lB).
Proof.
  destruct lB, kB, lA, kA.
  cbn in ql, qk.
  generalize ql^, qk^; clear ql qk.
  intros el ek; destruct el, ek.
  cbn in n |- *.
  lhs napply concat_1p.
  rhs napply concat_1p.
  exact (n @ concat_1p nB @ (concat_p1 nB)^).
Defined.

(** Change the homotopy at the center of an adjusted naturality square while preserving its two chosen endpoint paths. *)
Definition adjusted_naturality_comparison
  {X T : Type} {f g : X -> T} {x0 x1 : X} (r : x0 = x1)
  (A B : f == g) (H0 : f x0 = g x0) (H1 : f x1 = g x1)
  (lA : A x0 = H0) (kA : A x1 = H1)
  (lB : B x0 = H0) (kB : B x1 = H1)
  (q : forall x, A x = B x)
  (ql : q x0 = lA @ lB^) (qk : q x1 = kA @ kB^)
  : adjusted_naturality r A H0 H1 lA kA
    = adjusted_naturality r B H0 H1 lB kB
  := adjusted_square_comparison
    (fun e => e @ ap g r) (fun e => ap f r @ e)
    (concat_Ap A r) (concat_Ap B r) lA kA lB kB
    (q x0) (q x1) ql qk (concat_Ap_homotopic A B q r).

(** When the comparison is the ratio of two pointwise comparisons to one retained homotopy, the resulting square comparison is exactly the ratio of the specified adjusted-naturality witnesses. *)
Definition adjusted_naturality_comparison_homotopic
  {X T : Type} {f g : X -> T} {x0 x1 : X} (r : x0 = x1)
  (A B M : f == g)
  (h : forall x, A x = M x) (k : forall x, B x = M x)
  (q : forall x, A x = B x)
  (e : forall x, q x = h x @ (k x)^)
  : adjusted_naturality_comparison r A B (M x0) (M x1)
      (h x0) (h x1) (k x0) (k x1) q (e x0) (e x1)
    = adjusted_naturality_homotopic r A M h
      @ (adjusted_naturality_homotopic r B M k)^.
Proof.
  destruct r.
  unfold adjusted_naturality_comparison,
    adjusted_naturality_homotopic, adjusted_naturality,
    concat_Ap_homotopic.
  cbn.
  generalize (q x0), (e x0).
  snapply paths_ind_r.
  generalize (h x0), (k x0).
  generalize (M x0), (B x0).
  intros m b hx kx.
  destruct hx.
  revert b kx; snapply paths_ind_r.
  cbn.
  generalize (A x0).
  generalize (g x0).
  intros z p; destruct p.
  reflexivity.
Defined.

(** Transport a naturality square whose underlying homotopy is replaced at the target. The endpoint comparisons include the actual dependent paths of the two retained boundary homotopies. *)
Definition transport_adjusted_naturality
  {Z X T : Type} (f g : Z -> X -> T)
  {x0 x1 : X} (r : x0 = x1) {z0 z1 : Z} (p : z0 = z1)
  (A : forall x, f z0 x = g z0 x)
  (B : forall x, f z1 x = g z1 x)
  (H : forall z, f z x0 = g z x0)
  (K : forall z, f z x1 = g z x1)
  (l : A x0 = H z0) (k : A x1 = K z0)
  (q : forall x, transport (fun z => f z x = g z x) p (A x) = B x)
  : let l' := (q x0)^ @
      (ap (transport (fun z => f z x0 = g z x0) p) l @ apD H p) in
    let k' := (q x1)^ @
      (ap (transport (fun z => f z x1 = g z x1) p) k @ apD K p) in
    transport (fun z => ap (f z) r @ K z = H z @ ap (g z) r) p
      ((ap (fun e => ap (f z0) r @ e) k)^ @
        (concat_Ap A r @ ap (fun e => e @ ap (g z0) r) l))
    = (ap (fun e => ap (f z1) r @ e) k')^ @
        (concat_Ap B r @ ap (fun e => e @ ap (g z1) r) l').
Proof.
  destruct p, r; cbn.
  change (forall x, A x = B x) in q.
  generalize (q x0).
  generalize (B x0).
  intros b e; destruct e.
  cbn.
  assert (El : 1 @
      (ap (transport (fun z => f z x0 = g z x0) 1) l @ 1) = l).
  { lhs napply concat_1p.
    lhs napply concat_p1.
    apply ap_idmap. }
  assert (Ek : 1 @
      (ap (transport (fun z => f z x0 = g z x0) 1) k @ 1) = k).
  { lhs napply concat_1p.
    lhs napply concat_p1.
    apply ap_idmap. }
  rhs napply (ap011
    (fun (k0 : A x0 = K z0) (l0 : A x0 = H z0) =>
      (ap (fun e => 1 @ e) k0)^ @
      (concat_1p_p1 (A x0) @ ap (fun e => e @ 1) l0)) Ek El).
  reflexivity.
Defined.

(** The preceding transport agrees with the two canonical comparisons to a homotopy retained throughout the parameter path. This is the 4-dimensional naturality needed when the adjusted square is itself a face overlap. *)
Definition transport_adjusted_naturality_homotopic
  {Z X T : Type} (f g : Z -> X -> T)
  {x0 x1 : X} (r : x0 = x1) {z0 z1 : Z} (p : z0 = z1)
  (A : forall x, f z0 x = g z0 x)
  (B : forall x, f z1 x = g z1 x)
  (M : forall z x, f z x = g z x)
  (h : forall x, A x = M z0 x)
  (q : forall x, transport (fun z => f z x = g z x) p (A x) = B x)
  : let m := fun x => (q x)^ @
      (ap (transport (fun z => f z x = g z x) p) (h x)
        @ apD (fun z => M z x) p) in
    adjusted_naturality_homotopic r B (M z1) m
    = (transport_adjusted_naturality f g r p A B
        (fun z => M z x0) (fun z => M z x1) (h x0) (h x1) q)^
      @ (ap (transport
          (fun z => ap (f z) r @ M z x1 = M z x0 @ ap (g z) r) p)
          (adjusted_naturality_homotopic r A (M z0) h)
        @ apD (fun z => concat_Ap (M z) r) p).
Proof.
  destruct p, r.
  unfold adjusted_naturality_homotopic, adjusted_naturality,
    transport_adjusted_naturality.
  unfold transport.
  cbn.
  change (forall x, A x = B x) in q.
  set (qx := q x0) in *; clearbody qx.
  set (bx := B x0) in qx |- *; clearbody bx.
  clear q B.
  destruct qx.
  set (hx := h x0) in *; clearbody hx.
  set (mx := M z0 x0) in hx |- *; clearbody mx.
  clear h M.
  destruct hx.
  cbn.
  rhs napply concat_1p.
  rhs napply concat_p1.
  rhs napply ap_idmap.
  reflexivity.
Defined.

(** A transported rectangle followed by the induced top edge is its pointwise bottom-to-top comparison. The overlap coherence is retained explicitly. *)
Definition transport_rectangle_factor
  {A B : Type} (P : A -> B -> Type)
  {y0 y1 : A} (p : y0 = y1) {z0 z1 : B} (q : z0 = z1)
  (bottom : forall y, P y z0) (left : forall z, P y0 z)
  (overlap : bottom y0 = left z0)
  (top : forall y, P y z1)
  (qb : forall y, transport (P y) q (bottom y) = top y)
  (mt : top y0 = left z1)
  (coh : mt = (qb y0)^ @
    (ap (transport (P y0) q) overlap @ apD left q))
  : let cap := (apD bottom p)^ @
      ap (transport (fun y => P y z0) p) overlap in
    let U := fun z => transport (fun y => P y z) p (left z) in
    let edge := ap (transport (fun y => P y z1) p) mt^ @ apD top p in
    (ap (transport (P y1) q) cap @ apD U q) @ edge = qb y1.
Proof.
  destruct p, q.
  unfold transport in *; cbn in *.
  rewrite (ap_idmap overlap), (concat_1p overlap).
  rewrite (ap_idmap overlap), (concat_p1 overlap).
  rewrite (ap_V idmap mt), (ap_idmap mt), (concat_p1 mt^).
  pose (coh' := coh @
    (1 @@ (ap (fun r => r @ 1) (ap_idmap overlap)
      @ concat_p1 overlap))).
  lhs napply (1 @@ inverse2 coh').
  lhs napply (1 @@ inv_pp _ _).
  lhs napply (1 @@ (1 @@ inv_V _)).
  lhs napply concat_p_pp.
  lhs napply (concat_pV _ @@ 1).
  apply concat_1p.
Defined.

(** Variation of a five-face pasting, with an arbitrary dependent ambient type. The supplied dependent paths are the five chosen cubes, including the selected source face's cube. The construction only pastes them; it does not replace them by other inhabitants of the same types. *)
Section NaturalitySquareFillerVariation.
  Context {A : Type} {T : A -> Type}
    {x0 x1 x2 x3 y0 y1 y2 y3 : forall a, T a}
    {p0 : x0 == y0} {p1 : x1 == y1} {p2 : x2 == y2} {p3 : x3 == y3}
    {u0 : x0 == x1} {u1 : y0 == y1} {v0 : x2 == x3} {v1 : y2 == y3}
    {h0 : x0 == x2} {h1 : y0 == y2} {k0 : x1 == x3} {k1 : y1 == y3}
    (nu : forall a, p0 a @ u1 a = u0 a @ p1 a)
    (nv : forall a, p2 a @ v1 a = v0 a @ p3 a)
    (nh : forall a, p0 a @ h1 a = h0 a @ p2 a)
    (nk : forall a, p1 a @ k1 a = k0 a @ p3 a)
    (s : forall a, u0 a @ k0 a = h0 a @ v0 a).

  Let left a := concat_natural (p0 a) (p1 a) (p3 a)
    (u0 a) (u1 a) (k0 a) (k1 a).
  Let right a := concat_natural (p0 a) (p2 a) (p3 a)
    (h0 a) (h1 a) (v0 a) (v1 a).
  Let prefix a (n : p0 a @ (u1 a @ k1 a) = (u0 a @ k0 a) @ p3 a)
    (q : u0 a @ k0 a = h0 a @ v0 a) := n @ (q @@ 1).
  Let close a (n : p0 a @ (u1 a @ k1 a) = (h0 a @ v0 a) @ p3 a)
    (m : p0 a @ (h1 a @ v1 a) = (h0 a @ v0 a) @ p3 a)
    := cancelL (p0 a) _ _ (n @ m^).

  Definition naturality_square_filler_glue {a b : A} (p : a = b)
    (cu : transport _ p (nu a) = nu b)
    (cv : transport _ p (nv a) = nv b)
    (ch : transport _ p (nh a) = nh b)
    (ck : transport _ p (nk a) = nk b)
    (cs : transport _ p (s a) = s b)
    : transport (fun z => u1 z @ k1 z = h1 z @ v1 z) p
        (naturality_square_filler (nu a) (nv a) (nh a) (nk a) (s a))
      = naturality_square_filler (nu b) (nv b) (nh b) (nk b) (s b)
    := ap01D11 close p
      (ap01D11 prefix p (ap01D11 left p cu ck) cs)
      (ap01D11 right p ch cv).

  Definition apD_naturality_square_filler {a b : A} (p : a = b)
    : apD (fun z => naturality_square_filler
        (nu z) (nv z) (nh z) (nk z) (s z)) p
      = naturality_square_filler_glue p
        (apD nu p) (apD nv p) (apD nh p) (apD nk p) (apD s p).
  Proof.
    destruct p; reflexivity.
  Defined.
End NaturalitySquareFillerVariation.

(** [transport_naturality_square] with specified edge computations. Its hypotheses separate the two mixed computations, the two homotopy computations, and the geometric cube. This avoids repeating the beta-path bookkeeping when comparing maps defined by double recursion. *)
Definition transport_naturality_square_beta {A B : Type}
  {f0 f1 g0 g1 : A -> B}
  (u : f0 == f1) (v : g0 == g1)
  (h : f0 == g0) (k : f1 == g1)
  {x y : A} (p : x = y)
  {fh0 : f0 x = f0 y} {fh1 : f1 x = f1 y}
  {fv0 : f0 x = f1 x} {fv1 : f0 y = f1 y}
  {gh0 : g0 x = g0 y} {gh1 : g1 x = g1 y}
  {gv0 : g0 x = g1 x} {gv1 : g0 y = g1 y}
  (bfh0 : ap f0 p = fh0) (bfh1 : ap f1 p = fh1)
  (bfv0 : u x = fv0) (bfv1 : u y = fv1)
  (bgh0 : ap g0 p = gh0) (bgh1 : ap g1 p = gh1)
  (bgv0 : v x = gv0) (bgv1 : v y = gv1)
  (cf : fh0 @ fv1 = fv0 @ fh1)
  (cg : gh0 @ gv1 = gv0 @ gh1)
  (eh0 : fh0 @ h y = h x @ gh0)
  (eh1 : fh1 @ k y = k x @ gh1)
  (ev0 : fv0 @ k x = h x @ gv0)
  (ev1 : fv1 @ k y = h y @ gv1)
  (bf : concat_Ap u p @ (bfv0 @@ 1)
    = (1 @@ bfv1) @ naturality_change bfh0 bfh1 cf)
  (bg : concat_Ap v p @ (bgv0 @@ 1)
    = (1 @@ bgv1) @ naturality_change bgh0 bgh1 cg)
  (bh : concat_Ap h p = naturality_change bfh0 bgh0 eh0)
  (bk : concat_Ap k p = naturality_change bfh1 bgh1 eh1)
  (c : concat_natural fh0 fh1 gh1 fv0 fv1 (k x) (k y) cf eh1
      @ (ev0 @@ 1)
    = (1 @@ ev1) @ concat_natural fh0 gh0 gh1
      (h x) (h y) gv0 gv1 eh0 cg)
  : transport (fun z => u z @ k z = h z @ v z) p
      (naturality_change bfv0 bgv0 ev0)
    = naturality_change bfv1 bgv1 ev1.
Proof.
  napply (transport_naturality_square u v h k p).
  lhs napply (ap (concat_natural (ap f0 p) (ap f1 p) (ap g1 p)
    (u x) (u y) (k x) (k y) (concat_Ap u p)) bk @@ 1).
  rhs napply (1 @@ ap (fun q => concat_natural
    (ap f0 p) (ap g0 p) (ap g1 p)
    (h x) (h y) (v x) (v y) q (concat_Ap v p)) bh).
  exact (naturality_cube_change (h x) (h y) (k x) (k y)
    bfh0 bfh1 bfv0 bfv1 bgh0 bgh1 bgv0 bgv1
    _ _ cf cg eh0 eh1 ev0 ev1 bf bg c).
Defined.

(** A unit-based comparison transports to the comparison obtained from the two specified endpoint translations. The homotopies [Ny] and [Nv] retain the chosen unit path and translations. This only concerns a path starting at the distinguished unit parameter [e]. *)
Definition transport_translation_comparison {A T : Type}
  (e : A) (m : T -> A -> T) (ru : forall z, m z e = z)
  (rho : T -> T) (L : forall z, m z e = rho z)
  (f : T -> T) (E : forall z, f (rho z) = rho (f z))
  (y : T) {j : A} (p : e = j) (u v : T)
  (R0 : m y j = rho u) (R1 : m (f y) j = rho v)
  : let Ny := (ru u)^ @ (L u @ (R0^ @ (ap (m y) p^ @ ru y))) in
    let Nv := (ru v)^ @ (L v @ (R1^ @ (ap (m (f y)) p^ @ ru (f y)))) in
    transport (fun z => m (f y) z = f (m y z)) p
      (L (f y) @ (E y)^ @ ap f (L y)^)
    = R1 @ (ap rho (ap f Ny @ Nv^)^ @ ((E u)^ @ ap f R0^)).
Proof.
  assert (IsEquiv rho).
  { rapply (isequiv_homotopic idmap).
    exact (fun z => (ru z)^ @ L z). }
  destruct p.
  (** Equivalence/path induction normalizes the two free endpoint comparisons, with the unit case of each comparison still explicit. *)
  revert u R0.
  srapply (equiv_path_ind (fun u =>
    equiv_concat_l (L y) _ oE equiv_ap rho y u)).
  revert v R1.
  srapply (equiv_path_ind (fun v =>
    equiv_concat_l (L (f y)) _ oE equiv_ap rho (f y) v)).
  cbn.
  assert (K : forall {x y z : T} (a : x = y) (b : x = z),
    a^ @ (b @ ((b @ 1)^ @ (1 @ a))) = 1).
  { intros x0 y0 z0 a b; destruct a, b; reflexivity. }
  rhs napply (concat_p1 _ @@ 1).
  rhs napply (1 @@ (ap (fun q => ap rho q^)
    (ap011 (fun a b => ap f a @ b^) (K _ _ _ (ru y) (L y))
      (K _ _ _ (ru (f y)) (L (f y)))) @@ 1)).
  rhs napply (1 @@ concat_1p _).
  rhs napply (1 @@ (1 @@ ap (fun q => ap f q^) (concat_p1 (L y)))).
  apply concat_pp_p.
Defined.

(** The cube with unit vertex paths commutes for an arbitrary supplied comparison of zigzags. The four edges here are free; this does not eliminate a filler constrained to a fixed join boundary. *)
Definition concat_pV_cube_unit {T : Type} {x y z w : T}
  (p : x = y) (q : z = y) (r : x = w) (s : z = w)
  (h : p @ q^ = r @ s^)
  : concat_natural p s^ s^ r q^ 1 1 h
      (inverse_natural 1 1 (concat_1p_p1 s))
      @ ((concat_1p_p1 r)^ @@ 1)
    = (1 @@ inverse_natural 1 1 (concat_1p_p1 q))
      @ concat_natural p p s^ 1 1 r q^ (concat_1p_p1 p)^ h.
Proof.
  destruct p, r, s; cbn in *.
  revert h.
  equiv_intro (equiv_1p_q1 (p:=q^) (q:=1)) h.
  revert h.
  equiv_intro (equiv_path_inverse 1 q^) h.
  revert h.
  equiv_intro (equiv_ap inverse 1 q) h.
  destruct h; reflexivity.
Defined.

(** The unit cube with the vertical direction reversed. The double inverse in the upper vertical edge is part of the specified filler. *)
Definition concat_pV_cube_unit_inverse {T : Type} {x y z w : T}
  (p : x = y) (q : z = y) (r : x = w) (s : z = w)
  (h : p @ q^ = r @ s^)
  : let v := (1 @@ inv_V q)^ @ (inverse_natural p s^ h)^ in
    concat_natural s^ p p r^ q 1 1 v (concat_1p_p1 p)^
      @ (inverse_natural 1 1 (concat_1p_p1 r) @@ 1)
    = (1 @@ (concat_1p_p1 q)^)
      @ concat_natural s^ s^ p 1 1 r^ q
        (inverse_natural 1 1 (concat_1p_p1 s)) v.
Proof.
  destruct p, r, s; cbn in *.
  revert h.
  equiv_intro (equiv_1p_q1 (p:=q^) (q:=1)) h.
  revert h.
  equiv_intro (equiv_path_inverse 1 q^) h.
  revert h.
  equiv_intro (equiv_ap inverse 1 q) h.
  destruct h; reflexivity.
Defined.

(** Mapping a zigzag filler has the mixed computation determined by the four specified edge computations. Again all the edges, rather than the sides of a fixed diamond, are free in this path-algebra lemma. *)
Definition ap_pV_filler_beta {A B : Type} (f : A -> B)
  {x y z w : A} (p : x = y) (q : z = y) (r : x = w) (s : z = w)
  {p' : f x = f y} {q' : f z = f y} {r' : f x = f w} {s' : f z = f w}
  (bp : ap f p = p') (bq : ap f q = q')
  (br : ap f r = r') (bs : ap f s = s')
  (h : p @ q^ = r @ s^)
  : ap_naturality f h @ (br @@ 1)
    = (1 @@ (ap_V f q @ inverse2 bq))
      @ naturality_change bp (ap_V f s @ inverse2 bs)
        ((ap_pV f p q @ (bp @@ inverse2 bq))^
          @ (ap (ap f) h @ (ap_pV f r s @ (br @@ inverse2 bs)))).
Proof.
  destruct bp, bq, br, bs, p, r, s; cbn in *.
  revert h.
  equiv_intro (equiv_1p_q1 (p:=q^) (q:=1)) h.
  revert h.
  equiv_intro (equiv_path_inverse 1 q^) h.
  revert h.
  equiv_intro (equiv_ap inverse 1 q) h.
  destruct h; reflexivity.
Defined.

(** Turning a square exchanges its two pairs of opposite edges. *)
Definition turn_paths {A : Type} {a a' b b' : A}
  (p : a = b) (q : a = b') (r : a' = b) (s : a' = b')
  (h : p^ @ q = r^ @ s) : p @ r^ = q @ s^.
Proof.
  apply moveL_pV.
  lhs napply concat_pp_p.
  lhs_V napply (1 @@ h).
  apply concat_p_Vp.
Defined.

(** Map and turn a filler using the four specified reversed edge computations. *)
Definition turn_filler {A B : Type} (f : A -> B)
  {a a' b b' : A}
  (p : a = b) (q : a' = b) (r : a = b') (s : a' = b')
  {p' : f b = f a} {q' : f b = f a'}
  {r' : f b' = f a} {s' : f b' = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  (br : ap f r = r'^) (bs : ap f s = s'^)
  (h : p @ q^ = r @ s^)
  : p' @ r'^ = q' @ s'^
  := turn_paths p' q' r' s'
    ((1 @@ inv_V q')^
      @ ((ap_pV f p q @ (bp @@ inverse2 bq))^
        @ (ap (ap f) h @ (ap_pV f r s @ (br @@ inverse2 bs))))
      @ (1 @@ inv_V s')).

(** The composite-function transport calculation retains the actual application-composition path. *)
Definition equiv_naturality_transport_compose {A B C : Type}
  (f : A -> B) (g : B -> C) (h : A -> C)
  {x y : A} (p : x = y) (l : g (f x) = h x) (r : g (f y) = h y)
  (v : ap g (ap f p) @ r = l @ ap h p)
  : equiv_naturality_transport (g o f) h p l r
      ((ap_compose f g p @@ 1) @ v)
    = transport_paths_FFlFr p l
      @ moveR_Vp_p_inv (ap g (ap f p)) l (ap h p) r v.
Proof.
  destruct p.
  exact (ap (equiv_naturality_transport (g o f) h 1 l r) (concat_1p v)).
Defined.

(** Naturality along an inverse parameter path retains both inverse-application computations. *)
Definition concat_Ap_V {A B : Type} {f g : A -> B}
  (h : f == g) {x y : A} (p : x = y)
  : concat_Ap h p^
    = naturality_change (ap_V f p) (ap_V g p)
      (inverse_natural (h x) (h y) (concat_Ap h p)^).
Proof.
  destruct p; cbn.
  generalize (h x); generalize (g x).
  intros z q; destruct q; reflexivity.
Defined.

(** Reverse the parameter direction of a mixed computation, including the double inverse in the second horizontal edge. *)
Definition inverse_horizontal_mixed_beta {T : Type} {x y z w : T}
  {p p' : x = y} {q : y = w} {q' : w = y}
  {r r' : x = z} {s : z = w} {s' : w = z}
  (bp : p = p') (bq : q = q'^) (br : r = r') (bs : s = s'^)
  (h : p @ q = r @ s) (h' : p' @ q'^ = r' @ s'^)
  (v : h @ (br @@ 1) = (1 @@ bq) @ naturality_change bp bs h')
  : inverse_natural r q h^ @ (bq @@ 1)
    = (1 @@ br) @ naturality_change (inverse2 bp)
      (inverse2 bs @ inv_V s')
      (inverse_natural r' q'^ h'^ @ (1 @@ inv_V s')).
Proof.
  destruct bp, br.
  revert q bq s bs h v.
  snapply paths_ind_r.
  snapply paths_ind_r.
  intros h v.
  assert (k : h = h').
  { exact ((concat_p1 h)^ @ v
      @ (concat_1p _ @ (concat_p1 _ @ concat_1p _))). }
  destruct k; clear v.
  lhs napply concat_p1.
  rhs napply concat_1p.
  unfold naturality_change.
  rhs napply (concat_1p _ @@ 1).
  rhs napply (1 @@ inverse2 (ap (fun q => 1 @@ q) (concat_1p _))).
  symmetry; apply concat_pp_V.
Defined.

(** Compare the two orders of moving the edges in a reversed naturality square. *)
Definition inverse_natural_moves {T : Type} {x x' y y' : T}
  {p : x = y} {q : x' = y'} (h : x = x') (k : y = y')
  (n : h @ q = p @ k)
  : moveR_Vp h (k @ q^) p
      (moveL_pV q h (p @ k) n @ (concat_p_pp p k q^)^)
    = inverse_natural h k n.
Proof.
  destruct h, q, k.
  revert p n.
  srapply (equiv_path_ind (fun p =>
    equiv_ap (fun q => q @ 1) 1 p)).
  reflexivity.
Defined.

(** The two ways of reversing a zigzag square agree with rotation of its inverse. All four edges and the filler vary in this calculation. *)
Definition inverse_naturality_rotation {T : Type} {x y z w : T}
  (p : x = y) (q : z = y) (r : x = w) (s : z = w)
  (h : p @ q^ = r @ s^)
  : (1 @@ inv_V q)^ @ (inverse_natural p s^ h)^
    = inverse_natural q r^
        ((inv_pV p q)^ @ inverse2 (h^)^ @ inv_pV r s)
      @ (1 @@ inv_V p).
Proof.
  destruct p, q, r.
  revert s h.
  srapply (equiv_path_ind (fun s =>
    equiv_ap (fun q => 1 @ q^) 1 s)).
  reflexivity.
Defined.

(** The mixed computation of the inverse filler after a turn. This retains [ap_V] and the double-inverse computations, rather than treating the turn as a renaming of the square. *)
Definition turn_filler_beta {A B : Type} (f : A -> B)
  {a a' b b' : A}
  (p : a = b) (q : a' = b) (r : a = b') (s : a' = b')
  {p' : f b = f a} {q' : f b = f a'}
  {r' : f b' = f a} {s' : f b' = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  (br : ap f r = r'^) (bs : ap f s = s'^)
  (h : p @ q^ = r @ s^)
  : ap_naturality f h^ @ (bp @@ 1)
    = (1 @@ ((ap_V f s @ inverse2 bs) @ inv_V s'))
      @ naturality_change br ((ap_V f q @ inverse2 bq) @ inv_V q')
        ((1 @@ inv_V s')^
          @ (inverse_natural q' r'^
            (turn_filler f p q r s bp bq br bs h)^)^).
Proof.
  destruct p, r, s.
  revert p' bp q' bq r' br s' bs.
  revert h.
  equiv_intro (equiv_1p_q1 (p:=q^) (q:=1)) h.
  revert h.
  equiv_intro (equiv_path_inverse 1 q^) h.
  revert h.
  equiv_intro (equiv_ap inverse 1 q) h.
  destruct h.
  srapply (equiv_path_ind (fun p' => equiv_ap inverse 1 p')).
  srapply (equiv_path_ind (fun q' => equiv_ap inverse 1 q')).
  srapply (equiv_path_ind (fun r' => equiv_ap inverse 1 r')).
  srapply (equiv_path_ind (fun s' => equiv_ap inverse 1 s')).
  reflexivity.
Defined.

(** Mapping a turned filler can be computed before turning it. The inner and outer edge computations are retained separately, including the reversed inner edges. *)
Definition turn_filler_map {A B C : Type} (f : A -> B) (g : B -> C)
  {a a' b b' : A}
  (p : a = b) (q : a' = b) (r : a = b') (s : a' = b')
  {p' : f b = f a} {q' : f b = f a'}
  {r' : f b' = f a} {s' : f b' = f a'}
  (bp : ap f p = p'^) (bq : ap f q = q'^)
  (br : ap f r = r'^) (bs : ap f s = s'^)
  {p'' : g (f b) = g (f a)} {q'' : g (f b) = g (f a')}
  {r'' : g (f b') = g (f a)} {s'' : g (f b') = g (f a')}
  (cp : ap g p' = p'') (cq : ap g q' = q'')
  (cr : ap g r' = r'') (cs : ap g s' = s'')
  (h : p @ q^ = r @ s^)
  : (ap_pV g p' r' @ (cp @@ inverse2 cr))^
      @ (ap (ap g) (turn_filler f p q r s bp bq br bs h)
        @ (ap_pV g q' s' @ (cq @@ inverse2 cs)))
    = turn_paths p'' q'' r'' s''
      ((1 @@ inv_V q'')^
        @ ((ap_pV g p'^ q'^
              @ ((ap_V g p' @ inverse2 cp)
                @@ inverse2 (ap_V g q' @ inverse2 cq)))^
          @ (ap (ap g)
              ((ap_pV f p q @ (bp @@ inverse2 bq))^
                @ (ap (ap f) h @ (ap_pV f r s @ (br @@ inverse2 bs))))
            @ (ap_pV g r'^ s'^
              @ ((ap_V g r' @ inverse2 cr)
                @@ inverse2 (ap_V g s' @ inverse2 cs)))))
        @ (1 @@ inv_V s'')).
Proof.
  destruct cp, cq, cr, cs.
  (** Normalize the independent beta witnesses before eliminating source edges, so no motive quantifies over intermediate-universe witnesses. *)
  revert p' bp.
  srapply (equiv_path_ind (fun p' =>
    equiv_concat_l (inv_V (ap f p))^ _ oE equiv_ap inverse (ap f p)^ p')).
  revert q' bq.
  srapply (equiv_path_ind (fun q' =>
    equiv_concat_l (inv_V (ap f q))^ _ oE equiv_ap inverse (ap f q)^ q')).
  revert r' br.
  srapply (equiv_path_ind (fun r' =>
    equiv_concat_l (inv_V (ap f r))^ _ oE equiv_ap inverse (ap f r)^ r')).
  revert s' bs.
  srapply (equiv_path_ind (fun s' =>
    equiv_concat_l (inv_V (ap f s))^ _ oE equiv_ap inverse (ap f s)^ s')).
  destruct p, r, s.
  revert h.
  equiv_intro (equiv_1p_q1 (p:=q^) (q:=1)) h.
  revert h.
  equiv_intro (equiv_path_inverse 1 q^) h.
  revert h.
  equiv_intro (equiv_ap inverse 1 q) h.
  destruct h; reflexivity.
Defined.

Instance isequiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveR_pV p q r).
Proof.
  destruct p; apply isequiv_concat_lr.
Defined.

Definition equiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: (r = q @ p) <~> (r @ p^ = q)
:= Build_Equiv _ _ (moveR_pV p q r) _.

Instance isequiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_Mp p q r).
Proof.
  destruct r; apply isequiv_concat_lr.
Defined.

Definition equiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r^ @ q = p) <~> (q = r @ p)
:= Build_Equiv _ _ (moveL_Mp p q r) _.

Definition isequiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_pM p q r).
Proof.
  destruct p; apply isequiv_concat_lr.
Defined.

Definition equiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r <~> q = r @ p
  := Build_Equiv _ _ _ (isequiv_moveL_pM p q r).

Instance isequiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveL_Vp p q r).
Proof.
  destruct r; apply isequiv_concat_lr.
Defined.

Definition equiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: r @ q = p <~> q = r^ @ p
:= Build_Equiv _ _ (moveL_Vp p q r) _.

Instance isequiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveL_pV p q r).
Proof.
  destruct p; apply isequiv_concat_lr.
Defined.

Definition equiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: q @ p = r <~> q = r @ p^
:= Build_Equiv _ _ (moveL_pV p q r) _.

Definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_1M p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_M1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_1V p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_V1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Instance isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_1M p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition equiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
  : (1 = q @ p^) <~> (p = q)
  := Build_Equiv _ _ (moveR_1M p q) _.

Definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_1V p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_V1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.


Definition moveR_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : transport P p u = v)
  : moveR_transport_p P p u v (moveL_transport_V P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : u = transport P p^ v)
  : moveL_transport_V P p u v (moveR_transport_p P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Instance isequiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveR_transport_p P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveL_transport_V.
  - intro q; apply moveR_moveL_transport_V.
  - intro q; apply moveL_moveR_transport_p.
Defined.

Definition equiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: u = transport P p^ v <~> transport P p u = v
:= Build_Equiv _ _ (moveR_transport_p P p u v) _.


Definition moveR_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : transport P p^ u = v)
  : moveR_transport_V P p u v (moveL_transport_p P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : u = transport P p v)
  : moveL_transport_p P p u v (moveR_transport_V P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Instance isequiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveR_transport_V P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveL_transport_p.
  - intro q; apply moveR_moveL_transport_p.
  - intro q; apply moveL_moveR_transport_V.
Defined.

Definition equiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: u = transport P p v <~> transport P p^ u = v
:= Build_Equiv _ _ (moveR_transport_V P p u v) _.

Instance isequiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveL_transport_V P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveR_transport_p.
  - intro q; apply moveL_moveR_transport_p.
  - intro q; apply moveR_moveL_transport_V.
Defined.

Definition equiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: transport P p u = v <~> u = transport P p^ v
:= Build_Equiv _ _ (moveL_transport_V P p u v) _.

Instance isequiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveL_transport_p P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveR_transport_V.
  - intro q; apply moveL_moveR_transport_V.
  - intro q; apply moveR_moveL_transport_p.
Defined.

Definition equiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: transport P p^ u = v <~> u = transport P p v
:= Build_Equiv _ _ (moveL_transport_p P p u v) _.

Instance isequiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveR_equiv_M A B f _ x y).
Proof.
  unfold moveR_equiv_M.
  exact (isequiv_compose (ap f) (fun q => q @ eisretr f y)).
Defined.

Definition equiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (x = f^-1 y) <~> (f x = y)
  := Build_Equiv _ _ (@moveR_equiv_M A B f _ x y) _.

Instance isequiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveR_equiv_V A B f _ x y).
Proof.
  unfold moveR_equiv_V.
  exact (isequiv_compose (ap f^-1) (fun q => q @ eissect f y)).
Defined.

Definition equiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (x = f y) <~> (f^-1 x = y)
  := Build_Equiv _ _ (@moveR_equiv_V A B f _ x y) _.

Instance isequiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveL_equiv_M A B f _ x y).
Proof.
  unfold moveL_equiv_M.
  exact (isequiv_compose (ap f) (fun q => (eisretr f y)^ @ q)).
Defined.

Definition equiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (f^-1 y = x) <~> (y = f x)
  := Build_Equiv _ _ (@moveL_equiv_M A B f _ x y) _.

Instance isequiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveL_equiv_V A B f _ x y).
Proof.
  unfold moveL_equiv_V.
  exact (isequiv_compose (ap f^-1) (fun q => (eissect f y)^ @ q)).
Defined.

Definition equiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (f y = x) <~> (y = f^-1 x)
  := Build_Equiv _ _ (@moveL_equiv_V A B f _ x y) _.

(** Comparing two zigzag pastings eliminates their different intermediate endpoints. Only a spanning tree of the free edges is eliminated in the proof; the remaining closing edge is arbitrary. *)
Definition equiv_pasting_zigzags {T : Type}
  {x0 x1 y0 y1 z0 z1 u v : T}
  (p : x0 = y0) (q : x1 = y1) (r : x0 = z0) (s : x1 = z1)
  (a : y0 = u) (b : y1 = u) (c : z0 = v) (d : z1 = v)
  : ((p @ a) @ (q @ b)^ = (r @ c) @ (s @ d)^)
    <~> ((p^ @ r) @ c = a @ ((b^ @ (q^ @ s)) @ d)).
Proof.
  destruct p, q, r, s, a, b, c; cbn.
  exact (equiv_concat_r (concat_1p (1 @ d))^ (idpath _)
    oE (equiv_ap inverse (idpath _) (idpath _ @ d))^-1
    oE equiv_concat_r (concat_1p (1 @ d)^) (idpath _)).
Defined.

(** Common factors turn a comparison of pastings into a comparison of their remaining edge ratios. The four factorization witnesses are arbitrary and are used explicitly. *)
Definition equiv_pasting_factors {T : Type}
  {x0 x1 u v z0 z1 : T}
  (p : x0 = u) (q : x1 = u) (r : x0 = v) (s : x1 = v)
  (a : u = z0) (b : u = z1) (c : v = z0) (d : v = z1)
  {h : x0 = z0} {k : x1 = z1}
  (pa : p @ a = h) (qb : q @ b = k)
  (rc : r @ c = h) (sd : s @ d = k)
  : (a^ @ b = c^ @ d) <~> (p @ q^ = r @ s^).
Proof.
  assert (factor : forall {x y u v w : T}
    (p : x = u) (q : y = u) (a : u = v) (b : u = w)
    (h : x = v) (k : y = w),
    p @ a = h -> q @ b = k -> p @ q^ = (h @ (a^ @ b)) @ k^).
  { intros x y u0 v0 w p0 q0 a0 b0 h0 k0 f g.
    destruct p0, q0, a0, b0; cbn in *.
    destruct f, g; reflexivity. }
  exact (equiv_concat_lr (factor _ _ _ _ _ p q a b h k pa qb)
    (factor _ _ _ _ _ r s c d h k rc sd)^
    oE equiv_ap (concat_lr h k^) (a^ @ b) (c^ @ d)).
Defined.

(** *** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a path space, these dependent paths have a more convenient description: rather than transporting the left side both forwards and backwards, we transport both sides of the equation forwards, forming a sort of "naturality square".

   We use the same naming scheme as for the transport lemmas. *)

Definition dpath_path_l {A : Type} {x1 x2 y : A}
  (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  : q = p @ r
  <~>
  transport (fun x => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_r {A : Type} {x y1 y2 : A}
  (p : y1 = y2) (q : x = y1) (r : x = y2)
  : q @ p = r
  <~>
  transport (fun y => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lr {A : Type} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  : q @ p = p @ r
  <~>
  transport (fun x => x = x) p q = r.
Proof.
  destruct p; simpl.
  symmetry; apply equiv_p1_1q.
Defined.

Definition dpath_path_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  : q = ap f p @ r
  <~>
  transport (fun x => f x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_Fr {A B : Type} {g : A -> B} {x : B} {y1 y2 : A}
  (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  : q @ ap g p = r
  <~>
  transport (fun y => x = g y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : q @ ap g p = ap f p @ r
  <~>
  transport (fun x => f x = g x) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  - exact (equiv_concat_r (concat_1p r) (q @ 1)).
  - exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

(** A dependent naturality square, with the exact transport computation retained. *)
Definition dpath_path_FlFr_D {A : Type} {B : A -> Type}
  (f g : forall a, B a) {x y : A} (p : x = y)
  (u : f x = g x) (v : f y = g y)
  : (ap (transport B p) u @ apD g p = apD f p @ v)
    <~> (transport (fun z => f z = g z) p u = v)
  := equiv_concat_l (transport_paths_FlFr_D p u) v
    oE equiv_concat_l
      (concat_pp_p (apD f p)^ (ap (transport B p) u) (apD g p)) v
    oE equiv_moveR_Vp (ap (transport B p) u @ apD g p) v (apD f p).

(** Dependent naturality with two chosen source identifications. Their compatibility with the homotopy is essential: knowing only that the target values agree does not identify the adjusted paths. *)
Definition apD_homotopic_adjusted {A : Type} {B : A -> Type}
  {f g : forall x, B x} (K : f == g)
  {x y : A} (p : x = y) {b : B x}
  (h : f x = b) (k : g x = b) (coh : K x = h @ k^)
  : (ap (transport B p) h^ @ apD f p) @ K y
    = ap (transport B p) k^ @ apD g p.
Proof.
  destruct p; cbn.
  lhs napply (((ap_idmap h^ @@ 1) @ concat_p1 h^) @@ 1).
  rhs napply ((ap_idmap k^ @@ 1) @ concat_p1 k^).
  lhs napply (1 @@ coh).
  apply concat_V_pp.
Defined.

Definition dpath_path_FFlr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q @ p = ap g (ap f p) @ r
  <~>
  transport (fun x => g (f x) = x) p q = r.
Proof.
  destruct p; simpl.
  symmetry; apply equiv_p1_1q.
Defined.

Definition dpath_path_lFFr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q @ ap g (ap f p) = p @ r
  <~>
  transport (fun x => x = g (f x)) p q = r.
Proof.
  destruct p; simpl.
  symmetry; apply equiv_p1_1q.
Defined.

Definition dpath_paths2 {A : Type} {x y : A}
           (p : x = y) (q : idpath x = idpath x)
           (r : idpath y = idpath y)
: (concat_1p p)^ @ whiskerR q p @ concat_1p p
  = (concat_p1 p)^ @ whiskerL p r @ concat_p1 p
  <~>
  transport (fun a => idpath a = idpath a) p q = r.
Proof.
  destruct p. simpl.
  refine (_ oE equiv_cancelR _ _ 1).
  refine (_ oE equiv_cancelL 1 _ _).
  refine (equiv_concat_lr _ _).
  - symmetry; apply whiskerR_p1_1.
  - apply whiskerL_1p_1.
Defined.

(** ** Universal mapping property *)

Instance isequiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : IsEquiv (paths_ind a P) | 0.
Proof.
  refine (isequiv_adjointify (paths_ind a P) (fun f => f a 1) _ _).
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : P a 1 <~> forall x p, P x p
  := Build_Equiv _ _ (paths_ind a P) _.

Instance isequiv_paths_ind_r `{Funext} {A : Type} (a : A)
  (P : forall x, (x = a) -> Type)
  : IsEquiv (paths_ind_r a P) | 0.
Proof.
  refine (isequiv_adjointify (paths_ind_r a P) (fun f => f a 1) _ _).
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_ind_r `{Funext} {A : Type} (a : A)
  (P : forall x, (x = a) -> Type)
  : P a 1 <~> forall x p, P x p
  := Build_Equiv _ _ (paths_ind_r a P) _.

(** ** Truncation *)

(** Paths reduce truncation level by one.  This is essentially the definition of [IsTrunc_internal]. *)
