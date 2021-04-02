Require Import Basics Types.
Require Import Pointed.
Require Import Truncations.

Local Open Scope pointed_scope.

(** ** Encode-decode method *)

(** Encode-decode for loop spaces *)
Definition encode_decode_loops
  (A : Type) (a0 : A) (code : A -> Type)
  (c0 : code a0) (decode : forall x, code x -> a0 = x)
  (s : forall (c : code a0), decode _ c # c0 = c)
  (r : decode _ c0 = idpath)
  : a0 = a0 <~> code a0.
Proof.
  assert (t : forall x (p : point A = x), decode x (p # c0) = p).
  { intros x p.
    destruct p.
    exact r. }
  srapply equiv_adjointify.
  + exact (fun p => p # c0).
  + apply decode.
  + exact s.
  + rapply t.
Defined.

(** Variant using pointed types *)
Definition pointed_encode_decode_loop
  (A : pType) (code : pFam A)
  (decode : forall x, code x -> point A = x)
  (s : forall (c : code.1 (point A)), decode _ c # code.2 = c)
  (r : decode _ (pr2 code) = idpath)
  : loops A <~> code.1 (point A)
  := encode_decode_loops _ _ code.1 code.2 decode s r.

(** Encode-decode for truncated loop spaces *)
Definition encode_decode_trunc_loops n
  (A : Type) (a0 : A) (code : A -> Type) `{forall a, IsTrunc n (code a)}
  (c0 : code a0) (decode : forall x, code x -> Tr n (a0 = x))
  (s : forall (c : code a0), Trunc_rec (fun p => p # c0) (decode _ c) = c)
  (r : decode _ c0 = tr idpath)
  : Tr n (a0 = a0) <~> code a0.
Proof.
  (** Define the encode function. *)
  transparent assert (encode : (forall x, Tr n (a0 = x) -> code x)).
  { intros x.
    apply Trunc_rec.
    exact (fun p => p # c0). }
  assert (t : forall x (p : point A = x), decode x (encode _ (tr p)) = tr p).
  { intros x p.
    destruct p.
    exact r. }
  srapply equiv_adjointify.
  + apply encode.
  + apply decode.
  + exact s.
  + intros p.
    strip_truncations.
    apply t.
Defined.

(** Variant using pointed types *)
Definition pointed_encode_decode_trunc_loops n
  (A : pType) (code : pFam A) `{forall a, IsTrunc n (code a)}
  (decode : forall x, code x -> Tr n (point A = x))
  (s : forall (c : code.1 (point A)),
    Trunc_rec (fun (p : loops A) => p # code.2) (decode _ c) = c)
  (r : decode _ code.2 = tr idpath)
  : pTr n (loops A) <~> code (point A)
  := encode_decode_trunc_loops _ _ _ code.1 code.2 decode s r.




