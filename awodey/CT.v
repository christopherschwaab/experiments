Require Import Basics.
Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Relation_Definitions.
Require Import SetoidClass.
Open Scope program_scope.

Class Category :=
  { Obj : Type
  ; Hom : Obj -> Obj -> Type
  ; FEq : forall {A B : Obj}, relation (Hom A B)
  ; Equiv : forall A B : Obj, Equivalence (FEq (A:=A)(B:=B))
  ; comp : forall {A B C : Obj}, Hom B C -> Hom A B -> Hom A C
  ; comp_assoc : forall {A B C D : Obj} (f : Hom C D) (g : Hom B C) (h : Hom A B),
                   FEq (comp (comp f g) h) (comp f (comp g h))
  ; ident : forall A : Obj, Hom A A
  ; left_unit : forall {A B : Obj} (f : Hom A B), FEq (comp (ident B) f) f
  ; right_unit : forall {A B : Obj} (f : Hom A B), FEq (comp f (ident A)) f }.
Notation "f ⊚ g" := (comp f g) (at level 40, left associativity).
Notation "A ~> B" := (Hom A B) (at level 60, right associativity).
Notation "f ~~ g" := (FEq f g) (at level 50, no associativity).

Instance Hom_Setoid (C : Category) : forall X Y, Setoid (X ~> Y) :=
   {| equiv := fun f g => f ~~ g
    ; setoid_equiv := Equiv X Y |}.

Class Functor (C D : Category) :=
  { omap : @Obj C -> @Obj D
  ; fmap : forall {c1 c2 : @Obj C}, c1 ~> c2 -> omap c1 ~> omap c2
  ; fmap_id : forall c : @Obj C, fmap (ident c) ~~ @ident D (omap c)
  ; fmap_dist : forall {c1 c2 c3 : @Obj C} (f : c2 ~> c3) (g : c1 ~> c2),
                  fmap (f ⊚ g) ~~ fmap f ⊚ fmap g }.

Section Preorder.
  Class Preorder (P : Set) :=
    { Lt : P -> P -> Prop
    ; preorder_refl : forall a, Lt a a
    ; preorder_trans : forall {a b c}, Lt a b -> Lt b c -> Lt a c }.
  Instance Preoder_Category {P : Set} `{Preorder P} : Category :=
    {| Obj := P
     ; Hom := Lt
     ; FEq := fun A B (aLb aLb' : Lt A B) => eq aLb aLb'
     ; Equiv := fun A B => eq_equivalence
     ; comp := fun A B C bLc aLb => preorder_trans aLb bLc
     ; comp_assoc := fun A B C D f g h => proof_irrelevance _ _ _
     ; ident := preorder_refl
     ; left_unit := fun A B f => proof_irrelevance _ _ _
     ; right_unit := fun A B f => proof_irrelevance _ _ _ |}.
End Preorder.

Section Poset.
  Class Poset (A : Set) :=
    { Lte : A -> A -> Prop
    ; poset_refl : forall a, Lte a a
    ; poset_trans : forall {a b c}, Lte a b -> Lte b c -> Lte a c
    ; poset_antisym : forall {a b}, Lte a b -> Lte b a -> a = b }.
  Definition monotone {A B : Set} `{PA : Poset A}`{PB : Poset B} (m : A -> B) : Prop :=
    forall a a', Lte a a' -> Lte (m a) (m a').
  Definition monotone_comp {A B C : Set} `{PA : Poset A}`{PB : Poset B}`{PC : Poset C}
    {n : B -> C} {m : A -> B} : monotone n -> monotone m -> monotone (n ∘ m) :=
    fun mn mm a a' aLa' => mn _ _ (mm _ _ aLa').
  Instance Posets_Category : Category :=
    {| Obj := {A : Set & Poset A}
     ; FEq := fun A B f g => eq f g
     ; Equiv := fun A B => eq_equivalence
     ; Hom := fun (A B : sigT Poset) =>
               {f : projT1 A -> projT1 B | monotone (PA:=projT2 A)(PB:=projT2 B) f }
     ; comp := fun A B C f g => exist monotone (projT1 f ∘ projT1 g)
                                      (monotone_comp (projT2 f) (projT2 g))
     ; ident := fun A => exist monotone id (fun a a' aLa' => aLa') |}.
  Proof.
    intros A B C D f g h; simpl; reflexivity.
    intros A B f; destruct f; unfold monotone_comp, id, compose; simpl; f_equal.
    intros A B f; destruct f; unfold monotone_comp, id, compose; simpl; f_equal.
  Defined.
  
  Instance Poset_Category (P : Set) `{Poset P} : Category :=
    {| Obj := P
     ; Hom := Lte
     ; FEq := fun p1 p2 p1Lp2 p1Lp2' => eq p1Lp2 p1Lp2'
     ; Equiv := fun p1 p2 => eq_equivalence
     ; comp := fun p1 p2 p3 p2Lp3 p1Lp2 => poset_trans p1Lp2 p2Lp3
     ; comp_assoc := fun p1 p2 p3 p4 p3Lp4 p2Lp3 p1Lp2 => proof_irrelevance _ _ _
     ; ident := poset_refl
     ; left_unit := fun p1 p2 p1Lp2 => proof_irrelevance _ _ _
     ; right_unit := fun p1 p2 p1Lp2 => proof_irrelevance _ _ _ |}.
End Poset.

Module Type T0.
  Variable X : Set.
  Definition Subset (X : Set) := X -> Prop.
  Variable Tau : Subset X -> Prop.
  Definition Open (U : Subset X) := Tau U.

  Definition Empty : Subset X := fun x => False.
  Parameter Empty_open : Open Empty.

  Definition All (X : Set) : Subset X := fun x => True.
  Parameter X_open : Open (All X).
    
  Parameter Union_open : forall U V, Open U -> Open V -> Open (fun x => U x \/ V x).
  Parameter Intersection_open : forall U V, Open U -> Open V -> Open (fun x => U x /\ V x).
  
  Definition In (p : X) (S : Subset X) := S p.
  Definition Contains (S R : Subset X) := forall p, S p -> R p.
  Notation "S <= R" := (Contains S R) (at level 70, no associativity).

  Definition N (p : X) (V : Subset X) :=
    exists (U : Subset X), Open U /\ In p U /\ U <= V.
  Parameter Kolmogorov
    : forall p1 p2, p1 <> p2 -> (exists V, Open V /\ N p1 V /\ ~In p2 V ) \/
                                (exists V, Open V /\ N p2 V /\ ~In p1 V).
End T0.

Module Topology (Import t0 : T0).
  Hypothesis LEM : forall p1 p2 : X, p1 = p2 \/ p1 <> p2.

  Instance Specialization_Poset : Poset X :=
    {| Lte := fun x y => forall U, Open U -> In x U -> In y U |}.
  Proof.
    intros a U OU Ua; assumption.
    intros a b c aLb bLc U OU Ua; refine (bLc U OU _); apply (aLb U OU Ua).
    intros a b aLb bLa.
    assert (H : a = b \/ a <> b) by apply LEM; destruct H.
      assumption.
      assert ((exists V, Open V /\ N a V /\ ~In b V) \/
              (exists V, Open V /\ N b V /\ ~In a V)) by apply (Kolmogorov _ _ H).
      destruct H0; destruct H0 as [V H0]; destruct H0; destruct H1; destruct H1 as [W H1];
      destruct H1; destruct H3.
        assert (In b W) by apply (aLb W H1 H3).
        assert (In b V) by (apply H4; assumption).
        exfalso; apply H2; assumption.

        assert (In a W) by apply (bLa W H1 H3).
        assert (In a V) by (apply H4; assumption).
        exfalso; apply H2; assumption.
  Defined.
End Topology.

Instance Dis_Category (X : Set) : Category :=
  {| Obj := X
   ; Hom := fun x1 x2 => x1 = x2
   ; FEq := fun x1 x2 x1Ex2 x1Ex2' => eq x1Ex2 x1Ex2'
   ; Equiv := fun x1 x2 => eq_equivalence
   ; comp := fun x1 x2 x3 x2Ex3 x1Ex2 => eq_trans x1Ex2 x2Ex3
   ; comp_assoc := fun x1 x2 x3 x4 x1Ex2 x2Ex3 x3Ex4 => proof_irrelevance _ _ _
   ; ident := fun x => eq_refl
   ; left_unit := fun x1 x2 x1Ex2 => proof_irrelevance _ _ _
   ; right_unit := fun x1 x2 x1Ex2 => proof_irrelevance _ _ _ |}.

Class Monoid (M : Set) `{Setoid M} :=
  { mul : M -> M -> M
  ; one : M
  ; one_left : forall m, mul m one == m
  ; one_right : forall m, mul one m == m }.
Instance Monoids_Category : Category :=
  {||}.

Section Rel.
  Instance Rel_Category : Category :=
    {| Obj := Set
     ; Hom := fun (A B : Set) => A -> B -> Prop
     ; comp := fun A B C P Q => fun a c => exists b, P b c /\ Q a b
     ; ident := fun A => fun a b => a = b |}.
  Proof.
    intros A B C D P Q R; extensionality a; extensionality c.
    intros A B P; extensionality a; extensionality b.
    intros A B P. extensionality a; extensionality b.
End Rel.