Require Import Sumbool String List FMapInterface.

Variable var : Set.
Declare Module VarEqDec : DecidableType with Definition t := var.

Inductive typ : Set :=
| NumT : typ
| StrT : typ.

Inductive exp : Set :=
| V : var -> exp
| Num : nat -> exp
| Str : string -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp
| Cat : exp -> exp -> exp
| Len : exp -> exp
| Let_ : var -> exp -> exp -> exp.
Notation "e1 + e2" := (Plus e1 e2)
  (at level 50, left associativity).
Notation "e1 * e2" := (Times e1 e2)
  (at level 40, left associativity).
Notation "s1 ^ s2" := (Cat s1 s2)
  (at level 30, right associativity).
Notation "| e |" := (Len e)
  (at level 30, no associativity).

Declare Module M : WSfun VarEqDec.
Import M.
Definition ctx := t typ.

Reserved Notation "G |- e @ t" (at level 60, no associativity).
Inductive wtexp : ctx -> exp -> typ -> Prop :=
| OkVar : forall G x t, MapsTo x t G -> G |- V x @ t
| OkStr : forall G s, G |- Str s @ StrT
| OkNum : forall G n, G |- Num n @ NumT
| OkPlus : forall G e1 e2, G |- e1 @ NumT -> G |- e2 @ NumT -> G |- e1 + e2 @ NumT
| OkTimes : forall G e1 e2, G |- e1 @ NumT -> G |- e2 @ NumT -> G |- e1 * e2 @ NumT
| OkCat : forall G s1 s2, G |- s1 @ StrT -> G |- s2 @ StrT -> G |- s1 ^ s2 @ StrT
| OkLen : forall G s, G |- s @ StrT -> G |- |s| @ NumT
| OkLet : forall G e1 t1 e2 t2,
  G |- e1 @ t1 -> forall x, ~In x G -> add x t1 G |- e2 @ t2 -> G |- Let_ x e1 e2 @ t2
where "G |- e @ t" := (wtexp G e t).

Require Import Equality.

Axiom map_fun : forall x e e' (y : ctx), MapsTo x e y /\ MapsTo x e' y -> e = e'.

Lemma typing_unicity : forall G (e : exp) t,
  G |- e @ t -> forall t', G |- e @ t' -> t = t'.
Proof.
  intros G e t oke t' oke'.
  dependent induction oke; dependent destruction oke'; try reflexivity.
    apply (map_fun x t0 t1 G); split; assumption.
    cut (t1 = t0).
      destruct 1; apply IHoke2; assumption.
      apply IHoke1; assumption.
Qed.

Axiom nin_resp_eq : forall x y (m : ctx), VarEqDec.eq x y -> ~In x m -> ~In y m.
Definition EquivCtx G G' := Equiv (eq (A:=typ)) G G'.

Lemma unordered_ctx : forall G e t, G |- e @ t -> forall G', EquivCtx G G' -> G' |- e @ t.
Proof.
  intros G e t oke.
  induction oke; intros G' GEG'.
    destruct GEG'.
    assert (In x G') by (apply H0; exists t0; assumption); destruct H2.
    assert (t0 = x0) by (apply (H1 x t0 x0); assumption); destruct H3.
    apply OkVar; assumption.
    
    apply OkStr.
    apply OkNum.
    apply OkPlus; [apply IHoke1 | apply IHoke2]; assumption.
    apply OkTimes; [apply IHoke1 | apply IHoke2]; assumption.
    apply OkCat; [apply IHoke1 | apply IHoke2]; assumption.
    apply OkLen; apply IHoke; assumption.

    apply (OkLet _ _ t1).
      apply IHoke1; assumption.
      intro xInG'; destruct GEG'; apply H; apply H0; assumption.
      apply (IHoke2 (add x t1 G')).
      destruct GEG'.
      split; intros k; cut ({VarEqDec.eq x k} + {~VarEqDec.eq x k}).
        destruct 1; split; intro kInGx.
          exists t1; apply add_1; assumption.
          exists t1; apply add_1; assumption.

          destruct kInGx.
          assert (MapsTo k x0 G) by (apply (add_3 n H2)).
          assert (In k G') by (apply H0; exists x0; apply H3).
          destruct H4.
          exists x1.
          apply add_2; assumption.

          destruct kInGx.
          assert (MapsTo k x0 G') by (apply (add_3 n H2)).
          assert (In k G) by (apply H0; exists x0; apply H3).
          destruct H4.
          exists x1.
          apply add_2; assumption.
          
          apply VarEqDec.eq_dec.
          
        destruct 1; intros e0 e' kInG kInG'.
          assert (MapsTo k t1 (add x t1 G)) by (apply add_1; assumption).
          assert (MapsTo k t1 (add x t1 G')) by (apply add_1; assumption).
          assert (e0 = t1) by (apply (map_fun k e0 t1 (add x t1 G)); split; assumption).
          assert (e' = t1) by (apply (map_fun k e' t1 (add x t1 G')); split; assumption).
          rewrite H4, H5; reflexivity.

          assert (MapsTo k e0 G) by (apply (add_3 n kInG)).
          assert (MapsTo k e' G') by (apply (add_3 n kInG')).
          apply (H1 k e0 e' H2 H3).

          apply VarEqDec.eq_dec.
Qed.

Axiom add_swap : forall G (x1 : var) (t1 : typ) (x2 : var) (t2 : typ),
  EquivCtx (add x1 t1 (add x2 t2 G)) (add x2 t2 (add x1 t1 G)).
(*
Proof.
  intros G x1 t1 x2 t2; split; intro k.
    split; intro kInG.
      destruct kInG.
      exists x.
Qed.
*)

Lemma weakening : forall G e t,
  G |- e @ t -> forall x, ~In x G -> forall xt, add x xt G |- e @ t.
Proof.
  intros G e t oke.
  dependent induction oke; intros x1 x1Ng xt.
    apply OkVar; apply add_2;
      [intro xEx0; apply (nin_resp_eq _ _ _ xEx0) in x1Ng; apply x1Ng; exists t0 |];
      assumption.
    apply OkStr. 
    apply OkNum. 
    apply OkPlus; [apply IHoke1 | apply IHoke2]; assumption.
    apply OkTimes; [apply IHoke1 | apply IHoke2]; assumption.
    apply OkCat; [apply IHoke1 | apply IHoke2]; assumption.
    apply OkLen; apply IHoke; assumption.
    apply (OkLet _ _ t1).
      apply IHoke1; assumption.
      admit.
      admit.
Qed.

Import ListNotations.
Fixpoint fv' (vs : list var) (e : exp) : list var :=
  match e with
    | V x => if existsb (fun y => projT1 (bool_of_sumbool (VarEqDec.eq_dec x y))) vs
               then [x] else []
    | Num n => []
    | Str s => []
    | e1 + e2 => fv' vs e1 ++ fv' vs e2
    | e1 * e2 => fv' vs e1 ++ fv' vs e2
    | s1 ^ s2 => fv' vs s1 ++ fv' vs s2
    | Len e1 => fv' vs e1
    | Let_ y e1 e2 => fv' vs e1 ++ fv' (y :: vs) e2
  end.
Definition fv : exp -> list var := fv' [].

Program Fixpoint subst (b : exp) (x : var) (e : exp) : exp :=
  match e with
    | V y => match VarEqDec.eq_dec x y  with
               | left xEy => b 
               | right xNy => V y
             end
    | Num n => Num n
    | Str s => Str s
    | e1 + e2 => Plus (subst b x e1) (subst b x e2)
    | e1 * e2 => Times (subst b x e1) (subst b x e2)
    | s1 ^ s2 => Cat (subst b x s1) (subst b x s2)
    | Len e1 => Len (subst b x e1)
    | Let_ y e1 e2 => 
  end.