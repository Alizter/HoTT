Require Import Basics.
Require Import Types.
Require Import Modalities.ReflectiveSubuniverse.

(* Lemma 2.9 of CORS 

For a map g : X -> Y, the following are equivalent:

(1) g is an L-equivalence
(2) For any local type Z, the precomposition map g* : (Y -> Z) -> (X -> Z) is an equivalence.

*)

(* We can precompose maps in a commutative square to get another. *)
Definition comm_square_precompose `{Funext} {A B C D} {f : A -> B} {g : B -> D}
  {h : A -> C} {i : C -> D} (sq : g o f == i o h) (E : Type)
  : (fun j : _ -> E => j o f) o (fun j : _ -> E => j o g)
  == (fun j : _ -> E => j o h) o (fun j : _ -> E => j o i).
Proof.
  intro j.
  funext x.
  apply ap, sq.
Defined.

(* This bit lets us assume RSUs later *)
Module AssumeRSU (Ls : ReflectiveSubuniverses).
Import Ls.
Module Import Ls_Theory := ReflectiveSubuniverses_Theory Ls.
(* It can safely be completely ignored. *)

Section Lem_2_9.

  (* We assume funext and L to be a reflective subuniverse. *)
  Context `{Funext} (L : ReflectiveSubuniverse).

  (* f being an L-equivalence is written as O_inverts L f in the library *)

  (* Lemma 2.9 *)
  Lemma lemma_2_9 {X Y : Type} (g : X -> Y)
    : O_inverts L g <~> forall Z `{In L Z}, IsEquiv (fun h : Y -> Z => h o g).
  Proof.
    (* We have an equivalence of hprops so we only need back and forth maps. *)
    serapply equiv_iff_hprop.
    (* ==> *)
    { intro lequiv_g.
      intros Z islocal_Z.
      unfold O_functor in lequiv_g.
      set (natsq := to_O_natural L g).
      set (expsq := comm_square_precompose natsq Z).
      set (F := (fun j : L X -> Z => j o to L X)) in *.
      set (G := (fun j : Y -> Z => j o g)) in *.
      set (I := (fun j : L Y -> Z => j o to L Y)) in *.
      set (J := (fun j : L Y -> Z => j o O_functor L g)) in *.
      
      
      serapply isequiv_compose'. 
    
    
    admit. }
    (* <== *)
    { admit. }


End Lem_2_9.

End AssumeRSU.