Require Import Basics.Overture Basics.Tactics Basics.Equivalences
  Basics.PathGroupoids.
Require Import Types.Paths Types.Sigma.
Require Import Cubical.PathSquare Limits.Pullback.
Require Import WildCat.Core.
Require Import Pointed.Core Pointed.Loops Pointed.pEquiv.

Local Open Scope path_scope.
Local Open Scope pointed_scope.

(** * Pointed pullbacks *)

Definition pPullback {X Y Z : pType}
  (f : X ->* Z) (g : Y ->* Z) : pType
  := [Pullback f g,
      (point X; point Y; point_eq f @ (point_eq g)^)].

Definition ppullback_pr1 {X Y Z : pType}
  {f : X ->* Z} {g : Y ->* Z}
  : pPullback f g ->* X
  := Build_pMap pullback_pr1 1.

Definition ppullback_pr2 {X Y Z : pType}
  {f : X ->* Z} {g : Y ->* Z}
  : pPullback f g ->* Y
  := Build_pMap pullback_pr2 1.

Definition ppullback_commsq {X Y Z : pType}
  (f : X ->* Z) (g : Y ->* Z)
  : f o* ppullback_pr1 (f := f) (g := g)
    ==* g o* ppullback_pr2 (f := f) (g := g).
Proof.
  snapply Build_pHomotopy.
  - exact (pullback_commsq f g).
  - cbn.
    hott_simpl.
Defined.

Definition equiv_loops_ppullback {X Y Z : pType}
  (f : X ->* Z) (g : Y ->* Z)
  : loops (pPullback f g)
    <~> Pullback (fmap loops f) (fmap loops g).
Proof.
  pointed_reduce.
  refine (_ oE (equiv_path_pullback f g _ _)^-1%equiv).
  snapply equiv_functor_sigma_id.
  intros p.
  snapply equiv_functor_sigma_id.
  intros q.
  refine (equiv_concat_lr _ _ oE
    equiv_moveR_Vp _ _ _ oE sq_path^-1).
  - exact (ap (fun h => h^ @ (ap f p @ h))
      (concat_p1 _)^).
  - exact ((concat_p1 _)^ @ (concat_1p _)^).
Defined.

Definition loops_ppullback {X Y Z : pType}
  (f : X ->* Z) (g : Y ->* Z)
  : loops (pPullback f g)
    <~>* pPullback (fmap loops f) (fmap loops g).
Proof.
  snapply Build_pEquiv'.
  - exact (equiv_loops_ppullback f g).
  - destruct X as [X x0], Y as [Y y0], Z as [Z z0].
    pointed_reduce.
    hott_simpl.
    snapply path_sigma'.
    + reflexivity.
    + snapply path_sigma'.
      * reflexivity.
      * cbn.
        hott_simpl.
        generalize dependent (g y0).
        intros z p.
        destruct p.
        cbn.
        hott_simpl.
Defined.

Definition ppullback_corec
  {W X Y Z : pType} {f : X ->* Z} {g : Y ->* Z}
  (k : W ->* X) (l : W ->* Y)
  (p : f o* k ==* g o* l)
  : W ->* pPullback f g.
Proof.
  srapply Build_pMap.
  - exact (pullback_corec p).
  - napply equiv_path_pullback.
    snapply exist.
    + exact (point_eq k).
    + snapply exist.
      * exact (point_eq l).
      * napply sq_path.
        refine (concat_p_pp _ _ _ @ _).
        refine ((moveL_pV _ _ _ _)^).
        refine (concat_pp_p _ _ _ @ _).
        exact (point_htpy p).
Defined.

Definition ppullback_functor_commsq
  {X Y Z X' Y' Z' : pType}
  {f : X ->* Z} {g : Y ->* Z}
  {f' : X' ->* Z'} {g' : Y' ->* Z'}
  (h : Z ->* Z') (k : X ->* X') (l : Y ->* Y')
  (p : f' o* k ==* h o* f)
  (q : g' o* l ==* h o* g)
  : f' o* (k o* ppullback_pr1 (f := f) (g := g))
    ==* g' o* (l o* ppullback_pr2 (f := f) (g := g)).
Proof.
  transitivity ((f' o* k)
    o* ppullback_pr1 (f := f) (g := g)).
  - exact (pmap_compose_assoc f' k _)^*.
  - transitivity ((h o* f)
      o* ppullback_pr1 (f := f) (g := g)).
    + exact (pmap_prewhisker _ p).
    + transitivity (h o* (f o*
        ppullback_pr1 (f := f) (g := g))).
      * exact (pmap_compose_assoc h f _).
      * transitivity (h o* (g o*
          ppullback_pr2 (f := f) (g := g))).
        -- exact (pmap_postwhisker h (ppullback_commsq f g)).
        -- transitivity ((h o* g)
            o* ppullback_pr2 (f := f) (g := g)).
           ++ exact (pmap_compose_assoc h g _)^*.
           ++ transitivity ((g' o* l)
                o* ppullback_pr2 (f := f) (g := g)).
              ** exact (pmap_prewhisker _ q)^*.
              ** exact (pmap_compose_assoc g' l _).
Defined.

Definition ppullback_functor_commsq_point
  {X Y Z X' Y' Z' : pType}
  {f : X ->* Z} {g : Y ->* Z}
  {f' : X' ->* Z'} {g' : Y' ->* Z'}
  (h : Z ->* Z') (k : X ->* X') (l : Y ->* Y')
  (p : f' o* k ==* h o* f)
  (q : g' o* l ==* h o* g)
  (z : pPullback f g)
  : ppullback_functor_commsq h k l p q z
    = p z.1 @ ap h z.2.2 @ (q z.2.1)^.
Proof.
  cbn.
  hott_simpl.
Defined.

Definition functor_ppullback
  {X Y Z X' Y' Z' : pType}
  {f : X ->* Z} {g : Y ->* Z}
  {f' : X' ->* Z'} {g' : Y' ->* Z'}
  (h : Z ->* Z') (k : X ->* X') (l : Y ->* Y')
  (p : f' o* k ==* h o* f)
  (q : g' o* l ==* h o* g)
  : pPullback f g ->* pPullback f' g'.
Proof.
  napply ppullback_corec.
  exact (ppullback_functor_commsq h k l p q).
Defined.

Definition functor_ppullback_homotopy
  {X Y Z X' Y' Z' : pType}
  {f : X ->* Z} {g : Y ->* Z}
  {f' : X' ->* Z'} {g' : Y' ->* Z'}
  (h : Z ->* Z') (k : X ->* X') (l : Y ->* Y')
  (p : f' o* k ==* h o* f)
  (q : g' o* l ==* h o* g)
  : functor_ppullback h k l p q
    == functor_pullback f g f' g' h k l p q.
Proof.
  intros z.
  snapply path_sigma'.
  - reflexivity.
  - snapply path_sigma'.
    + reflexivity.
    + exact (ppullback_functor_commsq_point h k l p q z).
Defined.

Definition pequiv_ppullback
  {X Y Z X' Y' Z' : pType}
  {f : X ->* Z} {g : Y ->* Z}
  {f' : X' ->* Z'} {g' : Y' ->* Z'}
  (h : Z <~>* Z') (k : X <~>* X') (l : Y <~>* Y')
  (p : f' o* k ==* h o* f)
  (q : g' o* l ==* h o* g)
  : pPullback f g <~>* pPullback f' g'.
Proof.
  snapply Build_pEquiv.
  - exact (functor_ppullback h k l p q).
  - napply (isequiv_homotopic (equiv_pullback h k l p q)).
    + exact _.
    + intros z.
      refine (_ @ (functor_ppullback_homotopy h k l p q z)^).
      snapply path_sigma'.
      * reflexivity.
      * snapply path_sigma'.
        -- reflexivity.
        -- cbn.
           hott_simpl.
Defined.
