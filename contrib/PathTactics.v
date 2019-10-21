Require Import Basics Types.

Record Dep3x3 := {
                  B00 : Type; B04 : Type;
                  B40 : Type; B44 : Type;
                  B02 : B00 -> B04 -> Type;
                  B42 : B40 -> B44 -> Type;
                  B20 : B00 -> B40 -> Type;
                  B24 : B04 -> B44 -> Type;
                  B22 : forall b00 b44 b04 b40,
                      B02 b00 b04 ->
                      B42 b40 b44 ->
                      B20 b00 b40 ->
                      B24 b04 b44 -> Type;
                }.

(* Notation for identity map transport. *)
Notation coe p x := (transport idmap p x).

(* Here is the data that makes up the path type of a Dep3x3. *)
Record path_dep3x3 (u v : Dep3x3) := {
                                      p00 : u.(B00) = v.(B00);
                                      p04 : u.(B04) = v.(B04);
                                      p40 : u.(B40) = v.(B40);
                                      p44 : u.(B44) = v.(B44);
                                      p02 : forall x y, u.(B02) x y = v.(B02) (coe p00 x) (coe p04 y);
                                      p42 : forall x y, u.(B42) x y = v.(B42) (coe p40 x) (coe p44 y);
                                      p20 : forall x y, u.(B20) x y = v.(B20) (coe p00 x) (coe p40 y);
                                      p24 : forall x y, u.(B24) x y = v.(B24) (coe p04 x) (coe p44 y);
                                      p22 : forall b00 b44 b04 b40 b02 b42 b20 b24,
                                          u.(B22) b00 b44 b04 b40 b02 b42 b20 b24
                                          = v.(B22) (coe p00 b00) (coe p44 b44) (coe p04 b04) (coe p40 b40)
                                                    (coe (p02 b00 b04) b02)
                                                    (coe (p42 b40 b44) b42)
                                                    (coe (p20 b00 b40) b20)
                                                    (coe (p24 b04 b44) b24);
                                    }.

Ltac require_as_test_cps require if_yes if_no :=
  let res := match constr:(Set) with
             | _ => let __ := match constr:(Set) with _ => require () end in
                    ltac:(if_yes)
             | _ => ltac:(if_no)
             end in
  res ().
Ltac peel_evars term :=
  lazymatch term with
  | ?f ?x
    => require_as_test_cps ltac:(fun _ => has_evar x)
                                  ltac:(fun _ => peel_evars f)
                                         ltac:(fun _ => term)
  | _ => term
  end.

Ltac pi_to_sig ty :=
  lazymatch (eval cbv beta in ty) with
  | forall (x : ?T) (y : @?A x), @?P x y
    => let x' := fresh in
       constr:(@sigT T (fun x' : T => ltac:(let res := pi_to_sig (forall y : A x', P x' y) in exact res)))
  | ?T -> _ => T
  end.

Ltac ctor_to_sig ctor :=
  let ctor := peel_evars ctor in
  let t := type of ctor in
  pi_to_sig t.

Ltac unify_first_evar_with term u :=
  lazymatch term with
  | ?f ?x
    => tryif has_evar f
    then unify_first_evar_with f u
    else unify x u
  end.

Ltac unify_with_projections term u :=
  (unify_first_evar_with term u.1; unify_with_projections term u.2) +
  (unify_first_evar_with term u;
   tryif has_evar term then fail 0 term "has evars remaining" else idtac).

Ltac refine_with_existT_as_much_as_needed_then_destruct v :=
  ((destruct v; shelve) +
   (simple refine (_ ; _);
    [ destruct v; shelve
    | refine_with_existT_as_much_as_needed_then_destruct v ])).

Ltac issign :=
  hnf;
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  let u := fresh "u" in
  let v := fresh "v" in
  simple refine
         (BuildEquiv A B _
                     (BuildIsEquiv
                        A B
                        (fun u => _)
                        (fun v => _)
                        (fun v => _)
                        (fun u => _)
                        (fun _ => _)));
  [ let T := match goal with |- ?T => T end in
    let built := open_constr:(ltac:(econstructor) : T) in
    let A' := ctor_to_sig built in
    unify A A';
    unify_with_projections built u;
    refine built
  | refine_with_existT_as_much_as_needed_then_destruct v
  | destruct v; cbn [pr1 pr2]; reflexivity
  | reflexivity
  | reflexivity ].

Ltac refine_with_sigT_as_much_as_needed :=
  shelve + (refine (sigT _); intro; refine_with_sigT_as_much_as_needed).

Definition issig_path_dep3x3 {u v : Dep3x3}
  : _ <~> path_dep3x3 u v := ltac:(issign).

Definition issig_dep3x3
  : _ <~> Dep3x3 := ltac:(issign).

Definition equiv_path_dep3x3 `{Funext} {u v : Dep3x3}
  : path_dep3x3 u v <~> u = v.
Proof.
  symmetry.
  etransitivity; [ | apply issig_path_dep3x3 ].
  etransitivity;
  [ econstructor;
    apply @isequiv_ap
      with (f:=(@equiv_inv _ _ _ (@equiv_isequiv _ _ issig_dep3x3)));
    exact _ | ].
  unshelve (do 8 (etransitivity; [ symmetry; apply equiv_path_sigma | eapply equiv_functor_sigma'; intro ])); (* printing is insanely slow if you look at the proof inbetween these tactics *)
    cbv [issig_dep3x3 equiv_inv equiv_isequiv] in *; cbn [pr1 pr2] in *.
  1,2,3,4: repeat first [ solve [ reflexivity ]
                        | match goal with
                          | [ H : _ = _ |- _ ] => clear H || (destruct H; clear H; cbn [transport] in * )
                          end ].
  all: cbv [reflexivity reflexive_equiv equiv_idmap equiv_fun] in *.
  { repeat first [ solve [ reflexivity ]
                 | match goal with
                   | [ H : _ = _ |- _ ] => clear H || (destruct H; clear H; cbn [transport] in * )
                   end ].
  serapply equiv_equiv_path