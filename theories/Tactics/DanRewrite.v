(* A version of the rewrite tactic for equality goals that produces
   better proof terms.  See DanRewriteDemo.v for some examples.
   You use these like you use rewrite, but you specify whether you
   want to rewrite in the left-hand-side or right-hand-side of the goal.

   Currently can't specify which subterm is rewritten.

   Summary of user facing tactics:

   rewritel lem:     rewrite on lhs using lem from left to right
   rewritelV lem:    rewrite on lhs using lem from right to left
   rewriter lem:     rewrite on rhs using lem from left to right
   rewriterV lem:    rewrite on rhs using lem from right to left
   With s appended:  use syntatic_unify instead of unify when finding
                     the matching term.

   See rewrite_in_eqn_demo.v for examples.

   Written by Dan Christensen <jdc@uwo.ca> with help from
   Clément Pit-Claudel, Samuel Gruetter and others on the coq-club
   mailing list. *)

Require Import HoTT.Basics.

(* Replace a hypothesis in the context with the same hypothesis with
   all arguments filled in with new evars.  From
     http://adam.chlipala.net/cpdt/html/Cpdt.Match.html *)
Ltac insterU H :=
  repeat match type of H with
         | forall x : ?T, _ =>
           let x := fresh "arg" in
           evar (x : T);
           let x' := eval unfold x in x in
               clear x; specialize (H x')
         end.

(* The core of the tactic: finds a subterm of side matching src, abstracts it,
   and applies the passed in tactics. *)
Ltac _rewrite_helper side src lemH tac_unify tac_id tac_f :=
  match side with
  | context F[?trm] =>
    tac_unify src trm;
    let T := type of src in
    let f := constr:(fun w : T => ltac:(let t := context F[w] in exact t)) in
    (* Sometimes F has no CONTEXT-HOLE and so f is a constant function.
       I think this is a bug in Coq.  Detect this and force backtracking. *)
    tryif unify f (fun w : T => side) then fail else idtac;
    lazymatch f with
    | idmap => tac_id lemH
    | _ => tac_f f lemH
    end
  | _ => fail 0 src "unmatched"
  end.

(* Main tactic.  Behaves like rewrite, but produces cleaner proofs.
   tac_un is used to match one side of the given lemma with a sub-term.
   E.g. tac_un might be unify or syntactic_unify.
   tac_id and tac_f say what to do with the matched information.
   Called via notations below. *)
Ltac _rewrite_in_eqn side lem tac_unify tac_id tac_f :=
  (* It seems necessary to put the lemma in the context, rather than
     manipulating a Gallina term, since we need to use tactics to create evars.
     I think this leads to proof terms with lots of let ... := ... in ...
     These disappear definitionally, but are annoying.  *)
  let lemH := fresh "lemm" in
  epose lem as lemH;
  insterU lemH;
  lazymatch type of lemH with ?src = _ =>
    _rewrite_helper side src lemH tac_unify tac_id tac_f                              
  end;
  clear lemH.

(* A version for using a lemma in reverse. *)
Ltac _rewrite_in_eqnV side lem tac_unify tac_id tac_f :=
  (* It seems necessary to put the lemma in the context, rather than
     manipulating a Gallina term, since we need to use tactics to create evars.
     I think this leads to proof terms with lots of let ... := ... in ...
     These disappear definitionally, but are annoying.  *)
  let lemH := fresh "lemm" in
  epose lem as lemH;
  insterU lemH;
  lazymatch type of lemH with _ = ?src => (* only change *)
    _rewrite_helper side src lemH tac_unify tac_id tac_f                              
  end;
  clear lemH.

(* Specialized version for lhs. *)
Ltac _rewritel lem tac_un :=
  lazymatch goal with |- ?lhs = _ =>
    _rewrite_in_eqn lhs lem tac_un
                            ltac:(fun l => apply l || refine (l @ _))
                            ltac:(fun f l => refine (ap f l) || refine (ap f l @ _))
  end.

Tactic Notation "rewritel" open_constr(lem) := _rewritel lem ltac:(fun t1 t2 => unify t1 t2).

(* Specialized version for rhs. *)
Ltac _rewriter lem tac_un :=
  lazymatch goal with |- _ = ?rhs =>
    _rewrite_in_eqn rhs lem tac_un
                            ltac:(fun l => apply l^ || refine (_ @ l^))
                            ltac:(fun f l => refine ((ap f l)^) || refine (_ @ (ap f l)^))
  end.
(* While lem is used backwards above, it will appear to the user that
   it is being used forwards. *)

Tactic Notation "rewriter" open_constr(lem) := _rewriter lem ltac:(fun t1 t2 => unify t1 t2).

(* Now versions for using the lemma in reverse. *)
(* On the lhs, we end up with (ap f l)^ instead of (ap f l^). *)
Ltac _rewritelV lem tac_un :=
  lazymatch goal with |- ?lhs = _ =>
    _rewrite_in_eqnV lhs lem tac_un
                            ltac:(fun l => apply l^ || refine (l^ @ _))
                            ltac:(fun f l => refine (ap f l)^ || refine ((ap f l)^ @ _))
  end.

Tactic Notation "rewritelV" open_constr(lem) := _rewritelV lem ltac:(fun t1 t2 => unify t1 t2).

(* On the rhs, we end up with no inversions in the lemma. *)
Ltac _rewriterV lem tac_un :=
  lazymatch goal with |- _ = ?rhs =>
    _rewrite_in_eqnV rhs lem tac_un
                            ltac:(fun l => apply l || refine (_ @ l))
                            ltac:(fun f l => refine (ap f l) || refine (_ @ ap f l))
  end.

Tactic Notation "rewriterV" open_constr(lem) := _rewriterV lem ltac:(fun t1 t2 => unify t1 t2).

(* Next we give versions of the main tactics that force a strict
   syntactic unification of the endpoint of the path with a term in
   the goal.  The above methods are willing to unfold things, which
   can lead to surprises.  But the syntactic method here is often too
   strict, unable to match implicit arguments.  simpl and some unfolding
   can help when this happens. *)

(* From
     https://github.com/mit-plv/coqutil/blob/master/src/coqutil/Tactics/syntactic_unify.v
   I believe that this is supposed to be equivalent to
     unify x y; constr_eq x y
   which would figure out the unification variables, but then ensure
   that the unification was syntactic.  The goal of the following is
   to get this result more quickly by noticing syntactic differences
   before attempting full unification. *)
Ltac _syntactic_unify x y :=
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b =>
                        _syntactic_unify f g; _syntactic_unify a b end
         | (fun (a:?Ta) => ?f a) => lazymatch y with (fun (b:?Tb) => ?g b) => 
                        let __ := constr:(fun (a:Ta) (b:Tb) =>
                                            ltac:(_syntactic_unify f g; exact Set))
                        in idtac end
         | let a : ?Ta := ?v in ?f a => lazymatch y with let b : ?Tb := ?w in ?g b =>
                        _syntactic_unify v w;
                        let __ := constr:(fun (a:Ta) (b:Tb) =>
                                            ltac:(_syntactic_unify f g; exact Set))
                        in idtac end
         | _ => first [ constr_eq x y
                      | first [has_evar x | has_evar y]; unify x y; constr_eq x y ]
         end
  end.

Tactic Notation "syntactic_unify" open_constr(x) open_constr(y) :=  _syntactic_unify x y.

Tactic Notation "rewritels" open_constr(lem) := _rewritel lem ltac:(fun t1 t2 => syntactic_unify t1 t2).
Tactic Notation "rewritelVs" open_constr(lem) := _rewritelV lem ltac:(fun t1 t2 => syntactic_unify t1 t2).
Tactic Notation "rewriters" open_constr(lem) := _rewriter lem ltac:(fun t1 t2 => syntactic_unify t1 t2).
Tactic Notation "rewriterVs" open_constr(lem) := _rewriterV lem ltac:(fun t1 t2 => syntactic_unify t1 t2).
