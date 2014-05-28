Require Import Basics FunctionalExtensionality.
Open Scope program_scope.

Class Category :=
  { Obj : Type
  ; Hom : Obj -> Obj -> Type
  ; FEq : forall {A B : Obj}, Hom A B -> Hom A B -> Type
  ; comp : forall {A B C : Obj}, Hom B C -> Hom A B -> Hom A C
  ; comp_assoc : forall {A B C D : Obj} (f : Hom C D) (g : Hom B C) (h : Hom A B),
                   FEq (comp (comp f g) h) (comp f (comp g h))
  ; ident : forall A : Obj, Hom A A
  ; left_unit : forall {A B : Obj} (f : Hom A B), FEq (comp (ident B) f) f
  ; right_unit : forall {A B : Obj} (f : Hom A B), FEq (comp f (ident A)) f }.
Notation "f ⊚ g" := (comp f g) (at level 40, left associativity).
Notation "A ~> B" := (Hom A B) (at level 60, right associativity).
Notation "f ~~ g" := (FEq f g) (at level 50, no associativity).

Class Functor (C D : Category) :=
  { omap : @Obj C -> @Obj D
  ; fmap : forall {c1 c2 : @Obj C}{d1 d2 : @Obj D}, c1 ~> c2 -> d1 ~> d1 }.

Section Preorder.
  Class Preorder (P : Set) :=
    { Lt : P -> P -> Prop
    ; preorder_refl : forall a, Lt a a
    ; preorder_trans : forall {a b c}, Lt a b -> Lt b c -> Lt a c }.
  Instance Preoder_Category {P : Set} `{Preorder P} : Category :=
    {| Obj := P
     ; Hom := Lt
     ; FEq := fun A B (aLb aLb' : Lt A B) => True
     ; comp := fun A B C bLc aLb => preorder_trans aLb bLc
     ; comp_assoc := fun A B C D f g h => I
     ; ident := preorder_refl
     ; left_unit := fun A B f => I
     ; right_unit := fun A B f => I |}.
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
     ; FEq := fun p1 p2 p1Lp2 p1Lp2' => True
     ; comp := fun p1 p2 p3 p2Lp3 p1Lp2 => poset_trans p1Lp2 p2Lp3
     ; comp_assoc := fun p1 p2 p3 p4 p3Lp4 p2Lp3 p1Lp2 => I
     ; ident := poset_refl
     ; left_unit := fun p1 p2 p1Lp2 => I
     ; right_unit := fun p1 p2 p1Lp2 => I |}.
End Poset.

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