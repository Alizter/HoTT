Require Import Basics Types Spheres HSpace.
Require Import HomotopyGroup.
Require Import Spaces.Nat.

Local Open Scope nat_scope.

Require Import Pointed.
Require Import HIT.Truncations.
Import TrM.

Section bar.

  Context `{Univalence}.
  
  Require Import Smash.

  Local Open Scope pointed_scope.
  
  Notation pt := (point _).
  
 Definition Smash_rec_uncurried {P X Y : pType}
  :  {Psm : X -> Y -> P & {p : forall a, Psm a (point Y) = point P &
      {q : forall b, Psm (point X) b = point P & p pt = q pt}}}
    -> Smash X Y ->* P.
  Proof.
    intros [f [p [q coh]]].
    serapply Build_pMap.
    1: exact (Smash_rec' (Psm:=f) (fun x => p x @ (p pt)^)
      (fun x => q x @ (q pt)^) (concat_pV _) (concat_pV _)).
    apply p.
  Defined.

Require Import Cubical.

  Global Instance isequiv_Smash_rec_uncurried {P X Y : pType}
    : IsEquiv (Smash_rec_uncurried (P:=P) (X:=X) (Y:=Y)).
  Proof.
    serapply isequiv_adjointify.
    { intro f.
      refine (fun x y => f (sm x y); _).
      srefine (_;_;_).
      1,2: intro x; refine (_ @ point_eq f); apply ap.
      1: apply gluel'.
      1: apply gluer'.
      simpl.
      apply whiskerR.
      apply ap.
      unfold gluel', gluer'.
      refine (concat_pV _ @ (concat_pV _)^). }
    { intro f.
      apply path_pmap.
      serapply Build_pHomotopy.
      { serapply Smash_ind.
        1: reflexivity.
        1,2: simpl.
        1,2: apply ap.
        1: apply gluel.
        1: apply gluer.
        { simpl.
          intro x.
          apply dp_paths_FlFr.
          rewrite Smash_rec_beta_gluel.
          rewrite concat_p1.
          apply moveR_pM.
          refine (inv_pp _ _ @ _).
          apply moveR_Vp.
          refine (inv_pp _ _ @ _).
          destruct (point_eq f).
          rewrite concat_1p.
          unfold gluel'.
          rewrite ap_pp, ap_V.
          rewrite inv_pp.
          rewrite inv_V.
          rewrite concat_p_pp.
          apply whiskerR.
          refine ((concat_1p _)^ @ _).
          apply whiskerR.
          rewrite concat_p1.
          change (1^ = (ap f (gluel pt @ (gluel pt)^))^).
          apply inverse2.
          rewrite concat_pV.
          reflexivity. }
        simpl.
        intro b.
        apply dp_paths_FlFr.
        rewrite smash_rec_beta_gluer.
        rewrite concat_p1.
        apply moveR_pM.
        refine (inv_pp _ _ @ _).
        apply moveR_Vp.
        refine (inv_pp _ _ @ _).
        destruct (point_eq f).
        rewrite concat_1p.
        unfold gluer'.
        rewrite ap_pp, ap_V.
        rewrite inv_pp.
        rewrite inv_V.
        rewrite concat_p_pp.
        apply whiskerR.
        refine ((concat_1p _)^ @ _).
        apply whiskerR.
        rewrite concat_p1.
        rewrite concat_pV.
        reflexivity. }
      simpl.
      unfold gluel'.
      rewrite concat_pV.
      reflexivity. }
    intros [f [p [q coh]]].
    simpl.
    serapply path_sigma.
    1: reflexivity.
    cbn.
    serapply path_sigma_dp; simpl.
    { unfold Smash_rec'.
      apply path_forall.
      intro x.
      apply moveR_pM.
      refine (Smash_rec_beta_gluel' _ _ _ _ @ _).
      refine (_ @ concat_p1 _).
      apply whiskerL.
      change ((p pt @ (p pt)^)^ = 1^).
      apply inverse2.
      apply concat_pV. }
    apply dp_path_transport.
    rewrite transport_sigma.
    serapply path_sigma_dp; simpl.
    { unfold Smash_rec'.
      apply path_forall.
      intro y.
      cbn.
      rewrite transport_forall.
      rewrite transport_paths_FlFr.
      simpl.
      rewrite ap_const.
      rewrite Smash_rec_beta_gluer'.
      
      rewrite concat_pV.
      rewrite concat_p1.
      
      
    apply path_prod; simpl; apply path_forall; intro.
    1: rewrite Smash_rec_beta_gluel'.
    2: rewrite Smash_rec_beta_gluer'.
    1,2: hott_simpl.
    refine (_ @ concat_p1 _).
    rewrite concat_pp_p.
    apply whiskerL.
    
    
    apply moveR_Vp.
    rewrite concat_p1.
    destruct (p pt).
    destruct (q x).
    destruct (p pt).
    
  Admitted.
    
    
  Theorem foo `{HSpace X} `{IsConnected 1 X}
    : Tr 0 {x : _ & @HSpace X x} <~> Tr 0 (Smash X X ->* X).
  Proof.
    apply Trunc_functor_equiv.
    refine (BuildEquiv _ _ Smash_rec_uncurried _ oE _).
    (* TODO: issig HSpace, may require rewrite HSpace *)
    (* Since X is simply connected, we can rewrite the paths
       to match on both sides *)
      
    

Theorem foo n : {x : _ & @HSpace (psphere n) x} <~> Pi (n + n) (psphere n).
Proof.
  refine (_ oE _).
  { symmetry.
    apply equiv_pi_pmap. }
  (* Using the fact that smash rec uncurried is an equivalence we can show that
    HSpaces correspond to said maps *)

End bar.