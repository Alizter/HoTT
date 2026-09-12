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
