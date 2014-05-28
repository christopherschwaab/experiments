Require Import Sumbool String List FMapInterface Vector Equality Le Lt EqNat Plus Omega.

Inductive typ : Set :=
| NumT : typ
| StrT : typ.

Inductive exp : Set :=
| V : nat -> exp
| Num : nat -> exp
| Str : string -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp
| Cat : exp -> exp -> exp
| Len : exp -> exp
| Let_ : exp -> exp -> exp.
Notation "e1 + e2" := (Plus e1 e2)
  (at level 50, left associativity).
Notation "e1 * e2" := (Times e1 e2)
  (at level 40, left associativity).
Notation "s1 ^ s2" := (Cat s1 s2)
  (at level 30, right associativity).

Definition ctx := Vector.t typ.

Reserved Notation "G |- e @ t" (at level 60, no associativity).
Inductive wtexp : forall {n}, ctx n -> exp -> typ -> Prop :=
| OkVar : forall n (G : ctx n) (x : nat) (xLn : x < n), G |- V x @ nth_order G xLn
| OkStr : forall n (G : ctx n) s, G |- Str s @ StrT
| OkNum : forall n (G : ctx n) c, G |- Num c @ NumT
| OkPlus : forall n (G : ctx n) e1 e2,
  G |- e1 @ NumT -> G |- e2 @ NumT -> G |- e1 + e2 @ NumT
| OkTimes : forall n (G : ctx n) e1 e2,
  G |- e1 @ NumT -> G |- e2 @ NumT -> G |- e1 * e2 @ NumT
| OkCat : forall n (G : ctx n) s1 s2,
  G |- s1 @ StrT -> G |- s2 @ StrT -> G |- s1 ^ s2 @ StrT
| OkLen : forall n (G : ctx n) s, G |- s @ StrT -> G |- Len s @ NumT
| OkLet : forall n (G : ctx n) e1 t1 e2 t2,
  G |- e1 @ t1 -> Vector.cons _ t1 _ G |- e2 @ t2 -> G |- Let_ e1 e2 @ t2
where "G |- e @ t" := (wtexp G e t).

(*
Lemma nth_append_skip : forall {elt n m} (xs : Vector.t elt n) (ys : Vector.t elt m) xLm,
  nth_order (Vector.append xs ys) (n + x) = nth_order ys xLm.
Proof.
  intros elt n m xs ys x.
  induction x; induction n; dependent destruction xs; simpl; try reflexivity; apply IHn.
    intro; apply IHx.
Qed.
*)

(*
Lemma weaken_inv : forall {m} {G' : ctx m} {n} {G : ctx n} {x t},
  Vector.append G' G |- V (plusNat m x) @ t -> G |- V x @ nth G x.
Proof.
  intros m G' n G x t okv.
  dependent destruction okv; apply OkVar.
Qed.

Lemma typing_unicity : forall n (G : ctx n) (e : exp n) t,
  G |- e @ t -> forall t', G |- e @ t' -> t = t'.
Proof.
  intros n G e t oke t' oke'.
  dependent induction oke.
    dependent destruction oke'.
      reflexivity.
      apply nth_append_skip.
    assert (G |- V x @ nth G x) by apply OkVar.
    dependent destruction oke'.
      symmetry; apply nth_append_skip.
      reflexivity.
    cut (t1 = t0).
      destruct 1; apply IHoke2; assumption.
      apply IHoke1; assumption.
Qed.
*)

Lemma of_nat_lt_irr :
  forall n m (nLm1 nLm2 : n < m), Fin.of_nat_lt nLm1 = Fin.of_nat_lt nLm2.
Proof.
  induction n; intros m nLm1 nLm2; destruct m.
    inversion nLm1.
    reflexivity.
    inversion nLm1.
    unfold Fin.of_nat_lt.
    f_equal.
    apply IHn.
Qed.

Lemma nth_order_order_irr :
  forall {e} n (G : Vector.t e n) x (xLn : x < n) y (yLn : y < n),
    x = y -> nth_order G xLn = nth_order G yLn.
Proof.
  intros e n G x xLn y yLn xEy.
  destruct xEy.
  unfold nth_order, Fin.of_nat_lt.
  f_equal.
  apply of_nat_lt_irr.
Qed.

Lemma typing_unicity : forall n (G : ctx n) (e : exp) t,
  G |- e @ t -> forall t', G |- e @ t' -> t = t'.
Proof.
  intros n G e t oke t' oke'.
  dependent induction oke; dependent destruction oke'; try reflexivity.
    apply nth_order_order_irr; reflexivity.
    cut (t1 = t0).
      destruct 1; apply IHoke2; assumption.
      apply IHoke1; assumption.
Qed.

Fixpoint esuc (e : exp) : exp :=
  match e with
    | V x => V (1 + x)
    | Num c => Num c
    | Str s => Str s
    | c1 + c2 => esuc c1 + esuc c2
    | c1 * c2 => esuc c1 * esuc c2
    | s1 ^ s2 => esuc s1 ^ esuc s2
    | Len e1 => Len (esuc e1)
    | Let_ e1 e2 => Let_ (esuc e1) (esuc e2)
  end.

Fixpoint dist (n m : nat) :=
  match n, m with
    | n, O => n
    | O, m => m
    | S n', S m' => dist n' m'
  end.

(*
    m
Gl, t1, t2, Gr
==> |Gl| = m
==> x = m   => S x
    x = S m => x
*)

Fixpoint eswapn (m : nat) (e : exp) : exp :=
  match e with
    | V x =>
      if beq_nat x m then V (S m)
        else if beq_nat x (S m) then V m
          else V x
    | Num c => Num c
    | Str s => Str s
    | e1 + e2 => eswapn m e1 + eswapn m e2
    | e1 * e2 => eswapn m e1 * eswapn m e2
    | s1 ^ s2 => eswapn m s1 ^ eswapn m s2
    | Len e1 => Len (eswapn m e1)
    | Let_ e1 e2 => Let_ (eswapn m e1) (eswapn (S m) e2)
  end.
Definition eswap (e : exp) : exp := eswapn 0 e.

Lemma cons_append_comm : forall {e} x {n} (xs : Vector.t e n) {m} (ys : Vector.t e m),
  Vector.cons _ x _ (Vector.append xs ys) = Vector.append (Vector.cons _ x _ xs) ys.
Proof.
  intros e x n xs m ys.
  induction xs; simpl; reflexivity.
Qed.

Lemma eq_to_JMeq : forall A (x y : A), x = y -> x ~= y.
Proof.
  intros A x y xEy; rewrite xEy; reflexivity.
Qed.

Lemma strengthen_var : forall n (G : ctx n) x t t1,
  cons _ t1 _ G |- V (S x) @ t -> G |- V x @ t.
Proof.
  intros n G x t t1 okv.
  dependent destruction okv.
    unfold nth_order, nth.
    apply OkVar.
Qed.

Lemma nth_order_cons :
  forall {e n} (x : e) (xs : Vector.t e n) y (yLn : y < n) (SyLSn : S y < S n),
    nth_order xs yLn = nth_order (cons _ x _ xs) SyLSn.
Proof.
  intros e n x xs y yLn SyLSn.
  destruct y; destruct n.
    inversion yLn.
    reflexivity.
    inversion yLn.
    unfold nth_order, nth.
    simpl.
    f_equal.
    f_equal.
    apply of_nat_lt_irr.
Qed.

(* FIXME *)
Lemma nth_order_append :
  forall {e n} (ws : Vector.t e n) {m} (xs : Vector.t e m)
         y (yLm : y < m) z (zEp : z = y + n) (zL : z < n + m),
    nth_order xs yLm = nth_order (append ws xs) zL.
Proof.
  intros e n ws m xs y yLm z zL.
  induction ws.
    simpl; apply (nth_order_order_irr _ xs y yLm _ zL).
      rewrite plus_comm; reflexivity.
    rewrite <- cons_append_comm.
    rewrite (nth_order_cons ).
Qed.

Lemma weaken_var : forall n (G : ctx n) x t t1,
  G |- V x @ t -> cons _ t1 _ G |- V (S x) @ t.
Proof.
  intros n G x t t1 okv.
  dependent destruction okv.
    rewrite (nth_order_cons t1 _ _ _ (lt_n_S _ _ xLn)).
    apply OkVar.
Qed.

Lemma exchange : forall n (Gl : ctx n) m (Gr : ctx m) (e : exp) t t1 t2,
  Vector.append Gl (Vector.cons _ t1 _ (Vector.cons _ t2 _ Gr)) |- e @ t ->
  Vector.append Gl (Vector.cons _ t2 _ (Vector.cons _ t1 _ Gr)) |- eswapn (S n) e @ t.
Proof.
  intros n Gl m Gr e t t1 t2 oke.
  dependent induction oke.
  unfold eswapn.
  remember (beq_nat x (S n)).
  destruct b.
    assert (S n = x) by admit.
    destruct H.
    unfold nth_order, nth.
    simpl.
    
    

  induction n.
    destruct x.
      dependent destruction Gl.
      refine (OkVar _ (cons _ t2 _ (cons _ t1 _ Gr)) 1 _); apply lt_n_S; apply lt_0_Sn.
      destruct x.
        dependent destruction Gl.
        refine (OkVar _ (cons _ t2 _ (cons _ t1 _ Gr)) 0 _); apply lt_0_Sn.
        dependent destruction Gl.
        simpl in xLn.
        rewrite <- (nth_order_cons t1 (cons _ t2 _ Gr) _ (lt_S_n _ _ xLn) _).
        rewrite <- (nth_order_cons t2 Gr _ (lt_S_n _ _ (lt_S_n _ _ xLn)) _).
        apply weaken_var.
        apply weaken_var.
        apply OkVar.
    destruct x.
      destruct n.
      dependent destruction Gl.
      simpl.
      unfold nth_order, nth.
      simpl.
      assert (h = nth_order (cons typ h (S (S m)) (append Gl (cons typ t2 (S m) (cons typ t1 m Gr)))) xLn).
        unfold nth_order, nth.
        reflexivity.
      rewrite H.
      apply OkVar.
      simpl.
      dependent destruction Gl.
      unfold nth_order, nth.
      simpl.
      assert (h = nth_order (cons typ h (S (n + S (S m)))
                              (append Gl (cons typ t2 (S m) (cons typ t1 m Gr)))) xLn).
        unfold nth_order, nth.
        reflexivity.
      rewrite H.
      apply OkVar.



      

  destruct x.
    destruct n.
      dependent destruction Gl.
      simpl.
      refine (OkVar (S (S m)) (cons _ t2 _ (cons _ t1 _ Gr)) 1 _).
      apply le_n_S; apply le_n_S; apply le_0_n.
        destruct n; dependent destruction Gl.
          refine (OkVar _ (append (cons _ h _ Gl) (cons _ t2 _ (cons _ t1 _ Gr))) 0 _).
            apply le_n_S; apply le_0_n.
          refine (OkVar _ (append (cons _ h _ Gl) (cons _ t2 _ (cons _ t1 _ Gr))) 0 _).
            apply le_n_S; apply le_0_n.
      destruct n.
        dependent destruction Gl.
        destruct x.
          refine (OkVar _ (cons _ t2 _ (cons _ t1 _ Gr)) 0 _).
            apply le_n_S; apply le_0_n.
          simpl.
          simpl in xLn.
          rewrite <- (nth_order_cons t1 (cons _ t2 _ Gr) _ (lt_S_n _ _ xLn) _).
          rewrite <- (nth_order_cons t2 Gr _ (lt_S_n _ _ (lt_S_n _ _ xLn)) _).
          apply weaken_var.
          apply weaken_var.
          apply OkVar.
          simpl.
          dependent destruction Gl.
          destruct (dist x n).
 
        
| OkVar : forall n (G : ctx n) (x : nat) (xLn : x < n), G |- V x @ nth_order G xLn
        unfold nth_order, nth.
        simpl.
        apply OkVar.

    apply OkStr.
    apply OkNum.
    apply OkPlus; [apply IHoke1 | apply IHoke2]; reflexivity.
    apply OkTimes; [apply IHoke1 | apply IHoke2]; reflexivity.
    apply OkCat; [apply IHoke1 | apply IHoke2]; reflexivity.
    apply OkLen; apply IHoke; reflexivity.
    unfold eswap, eswapn.
    fold eswapn.
    apply (OkLet _ _ (eswapn n e1) t0 (eswapn (S n) e2)).
      apply IHoke1; reflexivity.
      rewrite cons_append_comm.
      apply (IHoke2 (S n) (cons _ t0 _ Gl) _ Gr t1 t2).
        reflexivity.
        apply eq_to_JMeq; apply cons_append_comm.
Qed.

Lemma weakening : forall n (G : ctx n) (e : exp n) t,
  G |- e @ t -> forall xt, Vector.cons _ xt _ G |- esuc e @ t.
Proof.
  intros n G e t oke.
  dependent induction oke; intros xt.
    apply (OkVar (S n) (Vector.cons _ xt _ G) (Fin.FS x)).
    apply OkStr. 
    apply OkNum. 
    simpl; apply OkPlus; [apply IHoke1 | apply IHoke2].
    apply OkTimes; [apply IHoke1 | apply IHoke2].
    apply OkCat; [apply IHoke1 | apply IHoke2].
    apply OkLen; apply IHoke.
    simpl. apply (OkLet (S n) (Vector.cons _ xt _ G) (esuc e1) t1).
      apply IHoke1.
      apply (IHoke2 t1).
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