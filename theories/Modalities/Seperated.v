Require Import Basics.
Require Import Types.
Require Import Modalities.ReflectiveSubuniverse.

Module Seperated_ReflectiveSubuniverse (Ls : ReflectiveSubuniverses)
  <: ReflectiveSubuniverses.

  Import Ls.
  (* We need the join construction to write down this universe with the correct levels *)
  Definition ReflectiveSubuniverse@{u a} := _ : Type2@{u a}.

  (* TODO *)
  Definition O_reflector : ReflectiveSubuniverse@{u a} -> Type@{i} -> Type@{i}
    := fun L => idmap.
(*     := fun O => Localize@{a i} (unLoc O). *)

  Definition In : ReflectiveSubuniverse@{u a} -> Type@{i} -> Type@{i}.
  Proof.
    intros L X.
    refine (forall (x y : X), _).
    exact (In L (x = y)).
  Defined.

  Definition O_inO : forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}),
    In O (O_reflector O T).
  Proof.
    
  
    := fun O => islocal_localize@{a i i} (unLoc O).

  Definition to :
    forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}), T -> O_reflector O T
    := fun O => @loc@{a i} (unLoc O).

  Definition inO_equiv_inO :
    forall (O : ReflectiveSubuniverse@{u a}) (T : Type@{i}) (U : Type@{j}),
      In@{u a i} O T -> forall f : T -> U, IsEquiv f ->
      In@{u a j} O U
    := fun O => islocal_equiv_islocal@{a i j i j k} (unLoc O).

  Definition hprop_inO@{u a i} `{Funext}
             (O : ReflectiveSubuniverse@{u a}) (T : Type@{i})
  : IsHProp (In@{u a i} O T).
  Proof.
    apply (@trunc_forall@{a i i} _); intros i.
    apply ishprop_ooextendable@{a a i i i  i i i i i  i i i}.
  Defined.

  Definition extendable_to_O
             (O : ReflectiveSubuniverse@{u a}) {P : Type@{i}}
             {Q : Type@{j}} {Q_inO : In@{u a j} O Q}
  : ooExtendableAlong@{i i j k} (to O P) (fun _ => Q).
  Proof.
    apply ext_localize_ind@{a i j i k}; intros ?.
    apply ooextendable_over_const.
    apply Q_inO.
  Defined.

End Seperated_ReflectiveSubuniverse.
