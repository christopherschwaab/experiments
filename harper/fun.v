Require Import Sumbool String List FMapInterface Vector.

Inductive typ : Set :=
| NumT : typ
| StrT : typ.

Inductive exp : nat -> Set :=
| V : forall {n}, Fin.t n -> exp n
| Num : forall {n}, nat -> exp n
| Str : forall {n}, string -> exp n
| Plus : forall {n}, exp n -> exp n -> exp n
| Times : forall {n}, exp n -> exp n -> exp n
| Cat : forall {n}, exp n -> exp n -> exp n
| Len : forall {n}, exp n -> exp n
| Let_ : forall {n}, exp n -> exp (S n) -> exp n.
Notation "e1 + e2" := (Plus e1 e2)
  (at level 50, left associativity).
Notation "e1 * e2" := (Times e1 e2)
  (at level 40, left associativity).
Notation "s1 ^ s2" := (Cat s1 s2)
  (at level 30, right associativity).

Definition ctx := Vector.t typ.

Fixpoint plusNat {n} (m : nat) (x : Fin.t n) : Fin.t (m + n) :=
  match m as m return Fin.t (m + n) with
    | O => x
    | S m' => Fin.FS (plusNat m' x)
  end.

Reserved Notation "G |- e @ t" (at level 60, no associativity).
Inductive wtexp : forall {n}, ctx n -> exp n -> typ -> Prop :=
| OkVar : forall n (G : ctx n) (x : Fin.t n), G |- V x @ nth G x
(*
| OkWeaken : forall m (G' : ctx m) n (G : ctx n) (x : Fin.t n),
  Vector.append G' G |- V (plusNat m x) @ nth G x
*)
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

Require Import Equality.

Lemma nth_append_skip : forall {elt n m} (xs : Vector.t elt n) (ys : Vector.t elt m) x,
  nth (Vector.append xs ys) (plusNat n x) = nth ys x.
Proof.
  intros elt n m xs ys x.
  induction x; induction n; dependent destruction xs; simpl; try reflexivity; apply IHn.
    intro; apply IHx.
Qed.

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

Lemma typing_unicity : forall n (G : ctx n) (e : exp n) t,
  G |- e @ t -> forall t', G |- e @ t' -> t = t'.
Proof.
  intros n G e t oke t' oke'.
  dependent induction oke; dependent destruction oke'; try reflexivity.
  cut (t1 = t0).
    destruct 1; apply IHoke2; assumption.
    apply IHoke1; assumption.
Qed.

Fixpoint esuc {n} (e : exp n) : exp (S n) :=
  match e with
    | V _ x => V (Fin.FS x)
    | Num _ c => Num c
    | Str _ s => Str s
    | c1 + c2 => esuc c1 + esuc c2
    | c1 * c2 => esuc c1 * esuc c2
    | s1 ^ s2 => esuc s1 ^ esuc s2
    | Len _ e1 => Len (esuc e1)
    | Let_ _ e1 e2 => Let_ (esuc e1) (esuc e2)
  end.

Fixpoint dist (n m : nat) :=
  match n, m with
    | n, O => n
    | O, m => m
    | S n', S m' => dist n' m'
  end.

Fixpoint eswapn {n} (m : nat) (e : exp (S (S n))) : exp (S (S n)) :=
  match e in exp n' return n' = S (S n) -> S (S n) = n' -> exp n' with
    | V _ x => fun eqN eqNr =>
      match dist (projT1 (Fin.to_nat x)) m with
        | O => eq_rect _ exp (V (Fin.FS Fin.F1)) _ eqNr
        | S O => eq_rect _ exp (V Fin.F1) _ eqNr
        | S (S x') => V x
      end
    | Num _ c => fun _ _ => Num c
    | Str _ s => fun _ _ => Str s
    | e1 + e2 => fun eqN eqNr =>
      eq_rect
        _ exp
        (eswapn m (eq_rect _ exp e1 _ eqN) + eswapn m (eq_rect _ exp e2 _ eqN))
        _ eqNr
    | e1 * e2 => fun eqN eqNr =>
      eq_rect
        _ exp
        (eswapn m (eq_rect _ exp e1 _ eqN) * eswapn m (eq_rect _ exp e2 _ eqN))
        _ eqNr
    | s1 ^ s2 => fun eqN eqNr =>
      eq_rect
        _ exp
        (eswapn m (eq_rect _ exp s1 _ eqN) ^ eswapn m (eq_rect _ exp s2 _ eqN))
        _ eqNr
    | Len _ e1 => fun eqN eqNr =>
      eq_rect
        _ exp
        (Len (eswapn m (eq_rect _ exp e1 _ eqN)))
        _ eqNr
    | Let_ _ e1 e2 => fun eqN eqNr =>
      eq_rect
        _ exp
        (Let_ (eswapn m (eq_rect _ exp e1 _ eqN))
              (eswapn (S m) (eq_rect _ (fun n => exp (S n)) e2 _ eqN)))
        _ eqNr
  end eq_refl eq_refl.
(*
  refine (
    let P (n : nat) (e : exp n) : Set :=
          match n with
            | O => unit
            | S O => unit
            | S (S n') => exp (S (S n'))
          end
    in exp_rec
         P
         (fun n x => match dist (projT1 (Fin.to_nat x)) m with
                       | O => _
                       | S O => _
                       | S (S x') => _
                     end)
         (fun n c => _)
         (fun n s => _)
         (fun n e1 e1' e2 e2' => _) (*e1' + e2'*)
         (fun n e1 e1' e2 e2' => _) (*e1' * e2'*)
         (fun n s1 s1' s2 s2' => _) (*s1' ^ s2'*)
         (fun n e1 e1' => _)
         (fun n e1 e1' e2 e2' => _)
         (S (S n)) e); destruct n0; try exact tt; try (destruct n0; try exact tt).
  simpl; exact (V (Fin.FS Fin.F1)).
  simpl; exact (V Fin.F1).
  simpl. exact (V (Fin.FS (Fin.FS x))).
  exact (Num c).
  exact (Str s).
  exact (e1' + e2').
  exact (e1' * e2').
  exact (s1' ^ s2').
  exact (Len e1').
  exact (Let_ e1' e2').
Defined.
*)
Definition eswap {n} (e : exp (S (S n))) : exp (S (S n)) := eswapn 0 e.

Fixpoint eswapn' {n} (m : nat) (okn : 2 <= n) (e : exp n) : exp n :=
  match e with
    | V _ x => fun eqN eqNr =>
      match dist (projT1 (Fin.to_nat x)) m with
        | O => eq_rect _ exp (V (Fin.FS Fin.F1)) _ eqNr
        | S O => eq_rect _ exp (V Fin.F1) _ eqNr
        | S (S x') => V x
      end
  end.
  

Lemma exchange : forall n (Gl : ctx n) m (Gr : ctx m) (e : exp (n + S (S m))) t t1 t2,
  Vector.append Gl (Vector.cons _ t1 _ (Vector.cons _ t2 _ Gr)) |- e @ t ->
  Vector.append Gl (Vector.cons _ t2 _ (Vector.cons _ t1 _ Gr)) |- eswap e @ t.
Proof.

Lemma exchange : forall n (G : ctx n) (e : exp (S (S n))) t t1 t2,
  Vector.cons _ t1 _ (Vector.cons _ t2 _ G) |- e @ t ->
  Vector.cons _ t2 _ (Vector.cons _ t1 _ G) |- eswap e @ t.
Proof.
  intros n G e t t1 t2 oke.
  dependent induction oke.
    unfold eswap, eswapn; simpl.
      dependent destruction x.
      apply OkVar.
      dependent destruction x.
      apply OkVar.

      (* FIXME *)
      assert (exists n', S (S n') = dist (projT1 (Fin.to_nat (Fin.FS (Fin.FS x)))) 0)
        by admit.
      destruct H.
      rewrite <- H.
      simpl.
      cut (nth (cons typ t2 (S n) (cons typ t1 n G)) (Fin.FS (Fin.FS x)) = nth G x).
        intro.
        rewrite <- H0.
        apply OkVar.
        apply (nth_append_skip (Vector.cons _ t2 _ (Vector.cons _ t1 _ (Vector.nil _)))
                               G x).
      apply OkStr.
      apply OkNum.
      apply OkPlus; [apply IHoke1 | apply IHoke2]; reflexivity.
      apply OkTimes; [apply IHoke1 | apply IHoke2]; reflexivity.
      apply OkCat; [apply IHoke1 | apply IHoke2]; reflexivity.
      apply OkLen; apply IHoke; reflexivity.
      apply (OkLet _ _ _ t0).
        apply IHoke1; reflexivity.
        fold (eswapn (n:=S n)).
        apply (IHoke2 _ (Vector.cons _ t1 _ G) _ t2 t0). reflexivity.
| OkLet : forall n (G : ctx n) e1 t1 e2 t2,
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