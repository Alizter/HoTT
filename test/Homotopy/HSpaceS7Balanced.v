From HoTT Require Import Basics Types.Prod Types.Universe.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Spaces.Spheres.
From HoTT Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.CayleyDickson.
From HoTT Require Import Homotopy.HSpaceS1 Homotopy.HSpaceS3.
From HoTT Require Import Homotopy.Join.Core Homotopy.HSpaceS7.Balanced.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The balanced law is not specific to the circle, needs no extensionality, and retains its supplied diamond and scalar corner paths. *)
Section GeneralScalars.
  Universe u.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative (@hspace_op X _)}
    `{!Commutative (@hspace_op X _)}
    (D : CayleyDicksonDiamond X (-)) (n : trunc_index)
    `{!IsConnected n X, !IsTrunc n.+1 X}.
  Local Existing Instance D.

  Check (@cd_op_balanced@{u} X _ _ _ D n _ _).
  Check (@cd_assoc_middle_joinl@{u} X _ _ _ D n _ _).

  Example balanced_small (s : X) (x y : Join@{u u u} X X)
    : cd_op (functor_join (.* s) (.* s) x) y
      = cd_op x (functor_join (s *.) (conj s *.) y)
    := cd_op_balanced n s x y.

  Example balanced_ll (s a c : X)
    : cd_op_balanced n s (joinl a) (joinl c)
      = ap joinl (cd_balanced_00 s a c) := idpath.
  Example balanced_lr (s a d : X)
    : cd_op_balanced n s (joinl a) (joinr d)
      = ap joinr (cd_balanced_01 s a mon_unit mon_unit d) := idpath.
  Example balanced_rl (s b c : X)
    : cd_op_balanced n s (joinr b) (joinl c)
      = ap joinr (cd_balanced_10 s b c) := idpath.
  Example balanced_rr (s b d : X)
    : cd_op_balanced n s (joinr b) (joinr d)
      = ap joinl (cd_balanced_11 s mon_unit b mon_unit d) := idpath.

  Example balanced_mixed (s a b c d : X)
    : transport011
        (fun x : X * X => fun y : X * X =>
          zigzag (fst x) (snd x) (fst y)
            = zigzag (fst x) (snd x) (snd y))
        (path_prod' (cd_balanced_00 s a c)
          (cd_balanced_11 s mon_unit b mon_unit d))
        (path_prod' (cd_balanced_01 s a mon_unit mon_unit d)
          (cd_balanced_10 s b c))
        (cd_op_diamond (a * s) (b * s) c d)
      = cd_op_diamond a b (s * c) (conj s * d)
    := cd_op_diamond_balanced_normalized n s a b c d.

  Example middle_associator (x y : Join@{u u u} X X) (s : X)
    : cd_op (cd_op x (joinl s)) y = cd_op x (cd_op (joinl s) y)
    := cd_assoc_middle_joinl n x s y.
End GeneralScalars.

Local Set Universe Minimization ToSet.

Section Circle.
  Context `{Univalence} (D : CayleyDicksonDiamond (psphere 1) (-)).
  Local Existing Instance D.

  (** There is no doubled-associativity or additional diamond-coherence input. *)
  Example circle_middle_associator (s : Sphere 1)
    (x y : Join@{Set Set Set} (Sphere 1) (Sphere 1))
    : cd_op@{Set} (X:=psphere 1) (cd_op x (joinl s)) y
      = cd_op x (cd_op (joinl s) y)
    := cd_assoc_middle_joinl (0%trunc) x s y.
End Circle.
