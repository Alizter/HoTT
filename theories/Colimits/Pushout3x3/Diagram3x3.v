Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import Colimits.Pushout.

(* 3x3 Diagram -- We can't use the Diagrams.Diagram since our diagrams commute up to homotopy. Therefore we would need a diagram over a graph with composition. Such as the one defined in Execuse 7.15.

The diagram looks like the following:

    A00 <--- A02 ---> A04
     ^     // ^ \\     ^
     |    //  |  \\    |
     |   VV   |   VV   |
    A20 <--- A22 ---> A24
     |   ^^   |   ^^   |
     |    \\  |  //    |
     V     \\ V //     V
    A40 <--- A42 ---> A44

The labels look like this:

    A00 f01 A02 f03 A04
    f10 H11 f12 H13 f14
    A20 f21 A22 f23 A24
    f30 H31 f32 H33 f34
    A40 f41 A42 f43 A44

We can shove all this data into the following record. *)

Record Diagram3x3 : Type := {
  A00 : Type; A02 : Type; A04 : Type;
  A20 : Type; A22 : Type; A24 : Type;
  A40 : Type; A42 : Type; A44 : Type;
  f01 : A02 -> A00; f03 : A02 -> A04;
  f10 : A20 -> A00; f12 : A22 -> A02; f14 : A24 -> A04;
  f21 : A22 -> A20; f23 : A22 -> A24;
  f30 : A20 -> A40; f32 : A22 -> A42; f34 : A24 -> A44;
  f41 : A42 -> A40; f43 : A42 -> A44;
  H11 : f01 o f12 == f10 o f21; H13 : f03 o f12 == f14 o f23;
  H31 : f41 o f32 == f30 o f21; H33 : f43 o f32 == f34 o f23;
}.

(* Notation for identity map transport. *)
Notation coe p x := (transport idmap p x).
(* 
Record path_Diagram3x3 (u v : Diagram3x3) := {
  p00 : u.(A00) = v.(A00); p02 : u.(A02) = v.(A02); p04 : u.(A04) = v.(A04);
  p20 : u.(A20) = v.(A20); p22 : u.(A22) = v.(A22); p24 : u.(A24) = v.(A24);
  p40 : u.(A40) = v.(A40); p42 : u.(A42) = v.(A42); p44 : u.(A44) = v.(A44);
  p01 : u.(f01) == v.(f01); p03 : u.(f03) = v.(f03);
  p10 : u.(f10) == v.(f10);

}.
  
  f01 : A02 -> A00; f03 : A02 -> A04;
  f10 : A20 -> A00; f12 : A22 -> A02; f14 : A24 -> A04;
  f21 : A22 -> A20; f23 : A22 -> A24;
  f30 : A20 -> A40; f32 : A22 -> A42; f34 : A24 -> A44;
  f41 : A42 -> A40; f43 : A42 -> A44;
  H11 : f01 o f12 == f10 o f21; H13 : f03 o f12 == f14 o f23;
  H31 : f41 o f32 == f30 o f21; H33 : f43 o f32 == f34 o f23;
}.
 *)
(* Now in Brunerie's thesis, the 3x3 lemma is proven direct using the data above. This made the proof very long and hard to follow (let alone write). We therefore opt for a more "type theoretic" approach in which we turn the edges of this diagram into type families over their corners and the middle type becomes a type family over these edges. What's nice is that this 3x3 diagram commutes definitionally since the maps are now projections. *)

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

Definition issig_Dep3x3 : _ <~> Dep3x3 := ltac:(issig).

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

Definition issig_path_dep3x3 {u v : Dep3x3}
  : _ <~> path_dep3x3 u v := ltac:(issig).

Definition equiv_path_dep3x3 `{Funext} {u v : Dep3x3}
  : path_dep3x3 u v <~> u = v.
Proof.
  symmetry.
  etransitivity.
  2: apply issig_path_dep3x3.
  
  etransitivity.
  { econstructor.
    apply @isequiv_ap with (f:=(@equiv_inv _ _ _
      (@equiv_isequiv _ _ issig_Dep3x3))); exact _. } 
    (* printing is insanely slow if you look at the proof inbetween these tactics *)
  unshelve (do 8 (etransitivity;
    [ symmetry; apply equiv_path_sigma
    | eapply equiv_functor_sigma'; intro ]));
    cbv [issig_Dep3x3 equiv_inv equiv_isequiv] in *; cbn [pr1 pr2] in *.
    
  1,2,3,4: repeat first
    [ solve [ reflexivity ]
    | match goal with
        | [ H : _ = _ |- _ ] => clear H 
          || (destruct H; clear H; cbn [transport] in * )
      end ].
  all: cbv [reflexivity reflexive_equiv equiv_idmap equiv_fun] in *.
  repeat first [ solve [ reflexivity ]
                 | match goal with
                   | [ H : _ = _ |- _ ] => clear H || (destruct H; clear H; cbn [transport] in * )
                   end ].
  simpl in *.
  
  symmetry.
  refine (issig_path_dep3x3 oE _).
  symmetry.
  

  serapply equiv_adjointify.
  1: shelve.
  { intros [].
    repeat (srefine (_;_); [reflexivity|]).
    cbn; reflexivity. }
  { intros []. cbv.
  
    repeat (refine (_;_); [reflexivity|]).
  
    repeat (serapply path_sigma'; [reflexivity| ]).
   destruct p.
  
  { rewrite <- (eisretr issig_Dep3x3 u).
    rewrite <- (eisretr issig_Dep3x3 v).
    intros [p00 [p04 [p40 [p44 [p02 [p42 [p20 [p24 p22]]]]]]]].
    apply ap.
    simpl in *.
    serapply (path_sigma' _ _).
    1: assumption.
    
    serapply path_sigma'.
    1: destruct p00.
    
    match goal with
     | [ |- transport _ ?p _ = _ ] => destruct p
    end.
    
    
    repeat (
    serapply (path_sigma' _ _); try assumption; cbn;
    match goal with
     | [ |- transport _ ?p _ = _ ] => destruct p
    end; cbn ).
    
    repeat (serapply path_sigma';
    [ funext x y; revert x y; assumption
    | match goal with
        | [ |- transport _ ?p _ = _ ] => destruct p
      end; cbn ]).
    

    rewrite transport_sigma.
    serapply path_sigma'.
    1: by refine (transport_const _ _ @ _).
    cbn.
    serapply transport_const.
    
    rewrite transportD_is_transport.
    rewrite transportD_is_transport.
    
    
    
    serapply path_sigma'.
    
    (rewrite transport_sigma;
    serapply path_sigma';
    [ by refine (transport_const _ _ @ _)
    | ]).
    
    simpl in *.
    rewrite transportD_is_transport.
    destruct p00.
    path_sigma'
(*     equiv_path_equiv
    
      
    1: funext ? ?; assumption.
    
    1: reflexivity.
    
    
    
    destruct (path_forall2 _ _ p02).
    destruct (path_forall2 _ _ p42).
    destruct (path_forall2 _ _ p20).
    destruct (path_forall2 _ _ p24).
    apply ap.
    funext ? ? ? ? ? ?.
    funext ? ?. *)
    Admitted.

(* Total space of two parameter type families. *)
Definition sig2 {X Y : Type} (A : X -> Y -> Type) := {x : X & {y : Y & A x y}}.
Arguments sig2 {X Y} A /.

(* Total space of 4 parameter type family over 2 parameter type families. *)
Definition sig42 {A B C D : Type}
  {a : A -> B -> Type} {b : C -> D -> Type}
  {c : A -> C -> Type} {d : B -> D -> Type} E :=
  {b00 : _ &
  {b44 : _ &
  {b04 : _ &
  {b40 : _ &
  {w : a b00 b04 &
  {x : b b40 b44 &
  {y : c b00 b40 &
  {z : d b04 b44 & E b00 b44 b04 b40 w x y z}}}}}}}}.
Arguments sig42 {_ _ _ _ _ _ _ _} E /.

(* Here is how to convert between a dependent 3x3 diagram and a regular 3x3 diagram. Note that stepping through this proof is very slow and it may be better to check the whole thing at once. *)
Definition Dep3x3_to_Pushout3x3 : Dep3x3 -> Diagram3x3.
Proof.
  intros [B00 B04 B40 B44 B02 B42 B20 B24 B22].
  (* We need to manually supply 25 bits of data. We start with the types and which we define as total spaces of the families. *)
  serapply (Build_Diagram3x3
        B00    (sig2 B02)     B04
    (sig2 B20) (sig42 B22) (sig2 B24)
        B40    (sig2 B42)     B44 _); cbn.
  (* Now we need to define the maps. We introduce the variable in order to quickly select the components. *)
  1,2,3,4,5,6,7,8,9,10,11,12: intro x.
  (* f01 *)
  1: exact x.1.
  (* f03 *)
  1: exact x.2.1.
  (* f10 *)
  1: exact x.1.
  (* f12 *)
  1: exact (x.1 ; x.2.2.1 ; x.2.2.2.2.1).
  (* f14 *)
  1: exact x.1.
  (* f21 *)
  1: exact (x.1 ; x.2.2.2.1 ; x.2.2.2.2.2.2.1).
  (* f23 *)
  1: exact (x.2.2.1 ; x.2.1 ; x.2.2.2.2.2.2.2.1).
  (* f30 *)
  1: exact x.2.1.
  (* f32 *)
  1: exact (x.2.2.2.1 ; x.2.1 ; x.2.2.2.2.2.1).
  (* f34 *)
  1: exact x.2.1.
  (* f41 *)
  1: exact x.1.
  (* f42 *)
  1: exact x.2.1.
  (* Finally all our homotopies commute by definition. *)
  all: reflexivity.
Defined.

(* Now what about the other way? *)
Definition Diagram3x3_to_Dep3x3 : Diagram3x3 -> Dep3x3.
Proof.
  intros [A00 A02 A04 A20 A22 A24 A40 A42 A44
    f01 f03 f10 f12 f14 f21 f23 f30 f32 f34 f41 f43
    H11 H13 H31 H33].
  serapply (Build_Dep3x3 A00 A04 A40 A44).
  + intros a00 a04.
    exact {x : _ & (f01 x = a00) * (f03 x = a04)}.
  + intros a40 a44.
    exact {x : _ & (f41 x = a40) * (f43 x = a44)}.
  + intros a00 a40.
    exact {x : _ & (f10 x = a00) * (f30 x = a40)}.
  + intros a04 a44.
    exact {x : _ & (f14 x = a04) * (f34 x = a44)}.
  + cbn.
    intros a00 a44 a04 a40
     [a02 [p01 p03]] [a42 [p41 p43]] [a20 [p10 p30]] [a24 [p14 p34]].
    refine {x : A22 & _}.
    refine {p12 : f12 x = a02 & _}.
    refine {p32 : f32 x = a42 & _}.
    refine {p21 : f21 x = a20 & _}.
    refine {p23 : f23 x = a24 & _}.
    refine (_ * _ * _ * _).
    - refine (Square (H11 x) (p01 @ p10^) (ap _ p12) (ap _ p21)).
    - refine (Square (H13 x) (p03 @ p14^) (ap _ p12) (ap _ p23)).
    - refine (Square (H31 x) (p41 @ p30^) (ap _ p32) (ap _ p21)).
    - refine (Square (H33 x) (p43 @ p34^) (ap _ p32) (ap _ p23)).
Defined.

Lemma foo {A B : Type} {C : A -> B -> Type} (x : A) (y : B)
  : {abc : {a : A & {b : B & C a b}} & (abc.1 = x) * (abc.2.1 = y)} = C x y.
Proof.
Admitted.

Definition dep_dia_dep `{Funext}
  : Sect Dep3x3_to_Pushout3x3 Diagram3x3_to_Dep3x3.
Proof.
  intros [B00 B04 B40 B44 B02 B42 B20 B24 B22].
  simpl.
  serapply equiv_path_dep3x3.
  serapply Build_path_dep3x3.
  all: simpl.
  1,2,3,4: reflexivity.
  all: simpl.
  1,2,3,4: apply foo.
  simpl.
Admitted.

Definition dia_dep_dia : Sect Diagram3x3_to_Dep3x3 Dep3x3_to_Pushout3x3.
Proof.
  intros [A00 A02 A04 A20 A22 A24 A40 A42 A44
    f01 f03 f10 f12 f14 f21 f23 f30 f32 f34 f41 f43 H11 H13 H31 H33].
  
Admitted.















