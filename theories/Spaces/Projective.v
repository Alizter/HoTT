Require Import Basics Types.
Require Import Truncations.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import HIT.Spheres.

Local Open Scope nat_scope.
Local Open Scope path_scope.

(** Projective spaces *)

(** ** Connected components of universes *)

(** We use the connected component of a universe in order to define X-bundles where X is a given type. *)

(** The connected component of a universe consists of all types that are merely equal to the given type [X]. *)
Record ConnectedComponent@{i j} (X : Type@{i}) := {
  type_conncomp : Type@{i} ;
  merely_path_type_conncomp : merely (@paths@{j} Type@{i} type_conncomp X) ;
}.

(** We coerce elements of connected components to the underlying universe. *)
Coercion type_conncomp : ConnectedComponent >-> Sortclass.

Definition issig_ConnectedComponent (X : Type)
  : _ <~> ConnectedComponent X := ltac:(issig).

Definition CC_base {X : Type} : ConnectedComponent X
  := Build_ConnectedComponent X X (tr idpath).

Definition equiv_path_cc {X : Type} {Y Z : ConnectedComponent X}
  : type_conncomp X Y = type_conncomp X Z <~> Y = Z.
Proof.
  etransitivity.
  2: exact (equiv_ap' (issig_ConnectedComponent X)^-1%equiv _ _)^-1%equiv.
  exact (equiv_path_sigma_hprop (_;_) (_;_)).
Defined.

(** An X-bundle on Y is a type family [Y -> U_X]. *)

(** The projective space construction is as follows *)

Section ProjConstruction.

  Context (X Y : Type) (cov : Y -> ConnectedComponent X)
    (l : forall x : Y, (*cov x ->*) (cov x : Type) = X).

  Definition ProjConstruction_type : Type.
  Proof.
    exact (Pushout (@pr1 Y cov) (fun _ => tt)).
  Defined.

  Definition ProjConstruction_cov
    : ProjConstruction_type -> ConnectedComponent X.
  Proof.
    snrapply (Pushout_rec _ cov (fun _ => CC_base)).
    intros [x y].
    simpl.
    unfold CC_base.
    apply equiv_path_cc.
    cbn.
    clear y.
    revert x.
(*     revert x y. *)
    apply l.
  Defined.

  Definition ProjConstruction_coh
    : forall x : ProjConstruction_type, (ProjConstruction_cov x : Type) = X.
  Proof.
    snrapply (Pushout_ind _ l (fun _ => 1)).
    intros xy.
    simpl.
    rewrite transport_paths_FlFr.
    rewrite ap_const.
    rewrite ap_compose.
    rewrite (Pushout_rec_beta_pglue _ _ _ _ xy).
    rewrite concat_p1.
    apply moveR_Vp.
    rewrite concat_p1.
    symmetry.
    destruct xy as [x y].
    simpl; hott_simpl.
    (** TODO: get rid of this nonsense *)
    refine ((ap_compose (fun u : {H : Type & rsu_reflector (modality_to_reflective_subuniverse (Tr (-1)))
      (H = X)} => {| type_conncomp := u.1; merely_path_type_conncomp := u.2 |}) (type_conncomp X) (@path_sigma_hprop Type (fun H : Type => rsu_reflector (modality_to_reflective_subuniverse (Tr (-1))) (H = X))
        (fun a : Type => istrunc_truncation (-1) (a = X))
        (type_conncomp X (cov x); merely_path_type_conncomp X (cov x)) (X; @tr (-1) (X = X) 1) 
        (l x)))^ @ _).
    simpl.
    rewrite ap_pr1_path_sigma_hprop.
    reflexivity.
  Defined.

End ProjConstruction.

(** Now we can bundle this all up and iterate as follows: *)

Section Projective.

  Context (X : Type).

  Record ProjectiveHelper := {
    projhelp_type : Type ;
    projhelp_cov : projhelp_type -> ConnectedComponent X;
    projhelp_coh : forall x, (projhelp_cov x : Type) = X;
  }.

  Definition ProjConstruction : ProjectiveHelper -> ProjectiveHelper.
  Proof.
    intros [Y cov coh].
    snrapply Build_ProjectiveHelper.
    + exact (ProjConstruction_type X Y cov).
    + exact (ProjConstruction_cov X Y cov coh).
    + exact (ProjConstruction_coh X Y cov coh).
  Defined.

  (** The base case is the same for all constructions *)
  (** In fact there is a (-1)-case but that doesn't seem to be useful, and is a pain to get working with nat *)

  Definition BaseCase : ProjectiveHelper.
  Proof.
    snrapply Build_ProjectiveHelper.
    + exact Unit.
    + exact (fun _ => CC_base).
    + intro; reflexivity.
  Defined.

  Fixpoint IteratedProjConstruction (n : nat) : ProjectiveHelper :=
    match n with
    | 0 => BaseCase
    | n.+1 => ProjConstruction (IteratedProjConstruction n)
    end.

End Projective.

Arguments projhelp_type {_}.
Arguments projhelp_cov {_}.
Arguments projhelp_coh {_}.

(** Characterization of the total space *)

Require Import Homotopy.Join.
(* Require Import HIT.Flattening. *)

(** Without univalence *)
Section Flattening.

  Context {A X Y U : Type} {f : A -> X} {g : A -> Y} (pr : U -> Type)
    (P_X : X -> U) (P_Y : Y -> U) (e : forall a, P_X (f a) = P_Y (g a)).

  Local Notation coe := (fun x => @transport _ pr _ _ (e x)).

  Definition pushout_family : Pushout f g -> U
    := Pushout_rec _ P_X P_Y e.

  Definition equiv_pushout_flattening `{Funext}
    : Pushout (functor_sigma (Q:=pr o P_X) f (fun _ => idmap)) (functor_sigma (Q:=pr o P_Y) g coe)
    <~> sig (pr o pushout_family).
  Proof.
  Admitted.

End Flattening.

Fixpoint IteratedJoin (n : nat) (X : Type) : Type :=
  match n with
  | 0 => Empty
  | 1%nat => X
  | n.+1 => Join (IteratedJoin n X) X
  end.

Section TotalSpace.

  Context `{Univalence}.

  Theorem equiv_sigma_proj_join (X : Type) (n : nat)
    : sig (projhelp_cov (IteratedProjConstruction X n)) <~> IteratedJoin n.+1 X.
  Proof.
    induction n.
    1: rapply equiv_contr_sigma.
    etransitivity ?[m].
    2: exact (equiv_functor_join IHn equiv_idmap).
    symmetry.
    change (
      Join {x : _ & projhelp_cov (IteratedProjConstruction X n) x} X 
       <~> {x : _ & projhelp_cov (ProjConstruction X (IteratedProjConstruction X n)) x}).
    unfold ProjConstruction.
    unfold projhelp_cov, projhelp_type.
    unfold ProjConstruction_type.
    unfold ProjConstruction_cov.
    pose @equiv_pushout_flattening as e.
    unfold pushout_family in e.

    specialize (e {x : projhelp_type (IteratedProjConstruction X n) &
      type_conncomp X (projhelp_cov (IteratedProjConstruction X n) x)}).
    specialize (e (projhelp_type (IteratedProjConstruction X n))).
    specialize (e Unit).
    specialize (e (ConnectedComponent X) ).
    specialize (e pr1 (fun _ => tt)).
    specialize (e (type_conncomp X)).
    specialize (e (projhelp_cov (IteratedProjConstruction X n))).
    specialize (e (unit_name CC_base)).
    specialize (e (fun
        a : {x0 : @projhelp_type X (IteratedProjConstruction X n) &
            type_conncomp X (@projhelp_cov X (IteratedProjConstruction X n) x0)} =>
      @equiv_fun
        (type_conncomp X (@projhelp_cov X (IteratedProjConstruction X n) a.1) =
         type_conncomp X {| type_conncomp := X; merely_path_type_conncomp := @tr (-1) (X = X) 1 |})
        (@projhelp_cov X (IteratedProjConstruction X n) a.1 =
         {| type_conncomp := X; merely_path_type_conncomp := @tr (-1) (X = X) 1 |})
        (@equiv_path_cc X (@projhelp_cov X (IteratedProjConstruction X n) a.1)
           {| type_conncomp := X; merely_path_type_conncomp := @tr (-1) (X = X) 1 |})
        (@projhelp_coh X (IteratedProjConstruction X n) a.1))).
    specialize (e _).
    
    refine (e oE _).
    clear e.
    snrapply equiv_pushout.
    { simpl.
      refine (equiv_sigma_assoc _ _ oE _).
      symmetry.
      refine (equiv_sigma_prod0 _ _ oE _).
      refine (equiv_sigma_assoc _ _ oE _).
      rapply equiv_functor_sigma_id.
      intros x.
      rapply equiv_functor_sigma_id.
      intro y.
      snrapply Build_Equiv.
      { intro z.
        
      1: intro a; exact y.
      simpl.
      
      Search prod "sigma".
    
      admit. }
    1: reflexivity.
    1: symmetry; rapply equiv_contr_sigma.
    { simpl. hnf.
    
    snrapply equiv_functor_pushout.
    
    Arguments Pushout : clear implicits.
    
    Search sum sig.


End TotalSpace.





(** Now we can get special cases *)

Section RealProjectiveSpace.

  Definition RealProjHelper := ProjSpaceConstruction (Sphere 0).

  Definition RealProjective (n : nat) : Type
    := projhelp_type (RealProjHelper n).

  Definition RealProjectiveCov (n : nat) : RealProjective n -> ConnectedComponent (Sphere 0)
    := projhelp_cov (RealProjHelper n).

End RealProjectiveSpace.

Section ComplexProjectiveSpace.

  Definition ComplexProjHelper := ProjSpaceConstruction (Sphere 1).

  Definition ComplexProjective (n : nat) : Type
    := projhelp_type (ComplexProjHelper n).

  Definition ComplexProjectiveCov (n : nat) : ComplexProjective n -> ConnectedComponent (Sphere 1)
    := projhelp_cov (ComplexProjHelper n).

End ComplexProjectiveSpace.

Section QuarternionicProjectiveSpace.

  Definition QuarternionicProjHelper := ProjSpaceConstruction (Sphere 3).

  Definition QuarternionicProjective (n : nat) : Type
    := projhelp_type (QuarternionicProjHelper n).

  Definition QuarternionicProjectiveCov (n : nat) : QuarternionicProjective n -> ConnectedComponent (Sphere 3)
    := projhelp_cov (QuarternionicProjHelper n).

End QuarternionicProjectiveSpace.
