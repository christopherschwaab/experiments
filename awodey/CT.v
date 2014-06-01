Require Import Basics.
Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Relation_Definitions.
Require Import SetoidClass.
Open Scope program_scope.

Lemma id_left_unit : forall {A B : Type} (f : A -> B), id ∘ f = f.
Proof. intros A B f; unfold compose; extensionality x; reflexivity. Qed.
Lemma id_right_unit : forall {A B : Type} (f : A -> B), f ∘ id = f.
Proof. intros A B f; unfold compose; extensionality x; reflexivity. Qed.

Class Category :=
  { Obj : Type
  ; Hom : Obj -> Obj -> Type
  ; HomSetoid :> forall X Y : Obj, Setoid (Hom X Y)
  ; comp : forall {A B C : Obj}, Hom B C -> Hom A B -> Hom A C
  ; comp_assoc : forall {A B C D : Obj} (f : Hom C D) (g : Hom B C) (h : Hom A B),
                   comp (comp f g) h == comp f (comp g h)
  ; comp_resp_equiv : forall {A B C : Obj},
                        Proper (equiv ==> equiv ==> equiv) (@comp A B C)
  ; ident : forall {A : Obj}, Hom A A
  ; ident_left_unit : forall {A B : Obj} (f : Hom A B), comp ident f == f
  ; ident_right_unit : forall {A B : Obj} (f : Hom A B), comp f ident == f }.
Notation "f ⊚ g" := (comp f g) (at level 40, left associativity).
Notation "A ~> B" := (Hom A B) (at level 60, right associativity).
Definition dom {C : Category} {A B : Obj} (f : A ~> B) := A.
Definition cod {C : Category} {A B : Obj} (f : A ~> B) := B.

Hint Extern 0 (Reflexive equiv) =>
  apply (@Equivalence_Reflexive _ _ (HomSetoid _ _)) : typeclass_instances.
Hint Extern 0 (Symmetric equiv) =>
  apply (@Equivalence_Symmetric _ _ (HomSetoid _ _)) : typeclass_instances.
Hint Extern 0 (Transitive equiv) =>
  apply (@Equivalence_Transitive _ _ (HomSetoid _ _)) : typeclass_instances.

Definition Inverse {C : Category} {A B : Obj} (f : A ~> B) (g : B ~> A) : Prop :=
  (f ⊚ g == ident) /\ (g ⊚ f == ident).
Definition Iso {C : Category} (A B : Obj) : Prop :=
  exists (f : A ~> B) (g : B ~> A), Inverse f g.
Notation "A ≅ B" := (Iso A B) (at level 50, no associativity).

Lemma comp_cong : forall {Cat : Category} {A B : Obj} {g h : A ~> B},
                    g == h -> forall {C} (f : Hom B C), f ⊚ g == f ⊚ h.
Proof. intros Cat A B g h gEh C f; apply comp_resp_equiv; [reflexivity | assumption]. Qed.

Lemma equiv_left_inv : forall {Cat : Category} {A B C : Obj} {g h : A ~> B} {f : B ~> C},
                         f ⊚ g == f ⊚ h -> forall {fi}, fi ⊚ f == ident -> g == h.
Proof.
  intros Cat A B C g h f fgEfh fi inv.
  transitivity (fi ⊚ f ⊚ g).
    transitivity (ident ⊚ g).
      symmetry; apply ident_left_unit.      
    apply comp_resp_equiv; [symmetry; assumption | reflexivity].
  transitivity (fi ⊚ f ⊚ h).
    repeat rewrite comp_assoc.
  apply comp_resp_equiv; [reflexivity | assumption].
  transitivity (ident ⊚ h).
    apply comp_resp_equiv; [assumption | reflexivity].
  apply ident_left_unit.
Qed.

Lemma ident_inverse : forall {C : Category} {A : Obj}, Inverse ident (ident (A:=A)).
Proof. intros C A; split; apply ident_left_unit. Qed.

Lemma inverse_uniqueness :
  forall {C : Category} {A B : Obj} (f : A ~> B) (g1 g2 : B ~> A),
    Inverse f g1 -> Inverse f g2 -> g1 == g2.
Proof.
  intros C A B f g1 g2 invG1 invG2.
  destruct invG1, invG2.
  rewrite <- H1 in H.
  apply (equiv_left_inv H H2).
Qed.

Lemma comp_inverse
  : forall {Cat : Category} {A B C : Obj} {f : B ~> C} {fi} {g : A ~> B} {gi},
      Inverse f fi -> Inverse g gi -> Inverse (f ⊚ g) (gi ⊚ fi).
Proof.
  intros Cat A B C f fi g gi finv ginv; split.
  transitivity (f ⊚ ident ⊚ fi).
  rewrite comp_assoc.
  apply comp_resp_equiv.
    symmetry; apply ident_right_unit.
  rewrite <- comp_assoc.
  destruct ginv.
  transitivity (ident ⊚ fi).
    apply comp_resp_equiv; [assumption | reflexivity].
  apply ident_left_unit.
  transitivity (f ⊚ fi).
    rewrite comp_assoc; apply comp_cong; apply ident_left_unit.
  destruct finv.
  assumption.

  transitivity (gi ⊚ ident ⊚ g).
  rewrite comp_assoc.
  apply comp_resp_equiv.
    symmetry; apply ident_right_unit.
  rewrite <- comp_assoc.
  destruct finv.
  transitivity (ident ⊚ g).
    apply comp_resp_equiv; [assumption | reflexivity].
  apply ident_left_unit.
  transitivity (gi ⊚ g).
    rewrite comp_assoc; apply comp_cong; apply ident_left_unit.
  destruct ginv.
  assumption.
Qed.

Lemma inverse_sym : forall {C : Category} {A B : Obj} {f : A ~> B} {fi : B ~> A},
                      Inverse f fi -> Inverse fi f.
Proof. intros C A B f fi finv; destruct finv; split; assumption. Qed.

Class Functor (C D : Category) :=
  { omap : @Obj C -> @Obj D
  ; fmap : forall {c1 c2 : @Obj C}, c1 ~> c2 -> omap c1 ~> omap c2
  ; fmap_id : forall c : @Obj C, fmap ident == @ident D (omap c)
  ; fmap_dist : forall {c1 c2 c3 : @Obj C} (f : c2 ~> c3) (g : c1 ~> c2),
                  fmap (f ⊚ g) == fmap f ⊚ fmap g }.

(*
Section Rel.
  Instance Rel_Category : Category :=
    {| Obj := Set
     ; Hom := fun (A B : Set) => A -> B -> Prop
     ; FEq := fun P Q => eq
     ; Equiv := fun P Q => eq_equivalence
     ; comp := fun A B C P Q => fun a c => exists b, P b c /\ Q a b
     ; ident := fun A => fun a b => a = b |}.
  Proof.
    intros A B C D P Q R; extensionality a; extensionality c.
    intros A B P; extensionality a; extensionality b.
    intros A B P. extensionality a; extensionality b.
End Rel.
*)

Section Preorder.
  Class Preorder (P : Set) :=
    { Lt : P -> P -> Prop
    ; preorder_refl : forall a, Lt a a
    ; preorder_trans : forall {a b c}, Lt a b -> Lt b c -> Lt a c }.
  Instance Preoder_Category {P : Set} `{Preorder P} : Category :=
    {| Obj := P
     ; Hom := Lt
     ; HomSetoid := fun A B => {| equiv := eq |}
     ; comp := fun A B C bLc aLb => preorder_trans aLb bLc
     ; comp_assoc := fun A B C D f g h => proof_irrelevance _ _ _
     ; comp_resp_equiv := fun a b c bLc bLc' _ aLb aLb' _ => proof_irrelevance _ _ _
     ; ident := preorder_refl
     ; ident_left_unit := fun A B f => proof_irrelevance _ _ _
     ; ident_right_unit := fun A B f => proof_irrelevance _ _ _ |}.
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
     ; HomSetoid := fun A B => {| equiv := eq |}
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
     ; HomSetoid := fun p1 p2 => {| equiv := eq |}
     ; comp := fun p1 p2 p3 p2Lp3 p1Lp2 => poset_trans p1Lp2 p2Lp3
     ; comp_assoc := fun p1 p2 p3 p4 p3Lp4 p2Lp3 p1Lp2 => proof_irrelevance _ _ _
     ; comp_resp_equiv := fun _ _ _ _ _ _ _ _ _ => proof_irrelevance _ _ _
     ; ident := poset_refl
     ; ident_left_unit := fun p1 p2 p1Lp2 => proof_irrelevance _ _ _
     ; ident_right_unit := fun p1 p2 p1Lp2 => proof_irrelevance _ _ _ |}.
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
   ; HomSetoid := fun x1 x2 => {| equiv := eq |}
   ; comp := fun x1 x2 x3 x2Ex3 x1Ex2 => eq_trans x1Ex2 x2Ex3
   ; comp_assoc := fun x1 x2 x3 x4 x1Ex2 x2Ex3 x3Ex4 => proof_irrelevance _ _ _
   ; comp_resp_equiv := fun _ _ _ _ _ _ _ _ _ => proof_irrelevance _ _ _
   ; ident := fun x => eq_refl
   ; ident_left_unit := fun x1 x2 x1Ex2 => proof_irrelevance _ _ _
   ; ident_right_unit := fun x1 x2 x1Ex2 => proof_irrelevance _ _ _ |}.

Section Monoid.
  Class Monoid (M : Type) `{Setoid M} :=
    { mul : M -> M -> M
    ; mul_assoc : forall m1 m2 m3, mul m1 (mul m2 m3) == mul (mul m1 m2) m3
    ; one : M
    ; one_left_unit : forall m, mul one m == m
    ; one_right_unit : forall m, mul m one == m }.

  Definition MonHom {M N : Type} `{MM : Monoid M} `{MN : Monoid N} (f : M -> N) :=
    Proper (equiv ==> equiv) f /\
    f one == one /\
    forall m1 m2, f (mul m1 m2) == mul (f m1) (f m2).

  Lemma comp_MonHom
    : forall {M N P : Type} `{Monoid M}`{Monoid N}`{Monoid P} {f : N -> P}{g : M -> N},
        MonHom f -> MonHom g -> MonHom (f ∘ g).
  Proof.
    intros M N P SM MM SN MN SP MP f g hf hg.
    destruct hf, hg.
    destruct H0, H2.
    split.
      intros x y xEy; unfold compose; repeat f_equiv; assumption.
      split.
        unfold compose; rewrite H2; assumption.
        intros m1 m2; unfold compose; rewrite H4; apply H3.
  Defined.
  
  Lemma id_MonHom : forall {M : Type} `{Monoid M}, MonHom id.
  Proof.
    intros M SM MM.
    split.
      intros x y xEy; assumption.
      split; [| intros]; reflexivity.
  Qed.

  Instance Monoids_Category : Category :=
    {| Obj := {Mon : Set & {SMon : Setoid Mon & Monoid Mon (H:=SMon)}}
     ; Hom := fun M N => sig (MonHom (H:=projT1 (projT2 M))(MM:=projT2 (projT2 M))
                                     (H0:=projT1 (projT2 N))(MN:=projT2 (projT2 N)))
     ; HomSetoid := fun M N => {| equiv := eq |}
     ; comp := fun M N P f g => existT _ (projT1 f ∘ projT1 g)
                                       (comp_MonHom (projT2 f) (projT2 g))
     ; ident := fun M => existT _ id id_MonHom |}.
  Proof.
    intros A B C D f g h; simpl; f_equal; apply proof_irrelevance.
    intros A B f; destruct f; destruct m; simpl; f_equal; apply proof_irrelevance.
    intros A B f; destruct f; simpl; f_equal; apply proof_irrelevance.
  Defined.
  
  Instance Comp_Monoid (X : Type) : forall S : Setoid (X -> X), Monoid (X -> X) :=
    {| mul := compose
     ; mul_assoc := fun m1 m2 m3 => reflexivity _
     ; one := id
     ; one_left_unit := fun m => reflexivity _
     ; one_right_unit := fun m => reflexivity _ |}.

  Class Group (G : Type) `{Monoid G} :=
    { inv : G -> G
    ; inv_inverse : forall g, mul (inv g) g == one }.
  Definition Aut {C : Category} (X : Obj) := {f : X ~> X & {g : X ~> X | Inverse f g}}.

  Instance Aut_Setoid {C : Category} (X : Obj) : Setoid (Aut X) :=
    {| equiv := fun f f' =>
         projT1 f == projT1 f' /\ projT1 (projT2 f) == projT1 (projT2 f')|}.
  Proof.
    split.
      intro; split; reflexivity.
      intros ? ? H; destruct H; split; symmetry; assumption.
      intros ? y ? H H0; destruct H, H0; split;
        [transitivity (projT1 y) | transitivity (projT1 (projT2 y))]; assumption.
  Defined.
  
  Definition aut_comp {C : Category} {X : Obj} (f g : Aut X) : Aut X :=
    existT _ (projT1 f ⊚ projT1 g)
          (exist _ (projT1 (projT2 g) ⊚ projT1 (projT2 f))
                 (comp_inverse (projT2 (projT2 f)) (projT2 (projT2 g)))).

  Instance Aut_Monoid {C : Category} (X : Obj) : Monoid (Aut X) :=
    {| mul := aut_comp
     ; one := existT _ ident (exist _ ident ident_inverse) |}.
  Proof.
    intros f g h; destruct f, g, h; simpl; split; [symmetry |]; apply comp_assoc.
    intro f; simpl; split; [apply ident_left_unit | apply ident_right_unit].
    intro f; simpl; split; [apply ident_right_unit | apply ident_left_unit].
  Defined.

  Definition aut_inv {C : Category} {X : Obj} (f : Aut X) : Aut X :=
    existT _ (projT1 (projT2 f))
           (exist _ (projT1 f) (inverse_sym (projT2 (projT2 f)))).
  Instance Aut_Group {C : Category} (X : Obj) : Group (Aut X) :=
    {| inv := aut_inv |}.
  Proof.
    intros g; destruct g; destruct s; destruct i; simpl; split; assumption.
  Defined.
  
  Instance Perm_Setoid {C : Category} (X : Obj) (P : Aut X -> Prop)
    : Setoid {g : Aut X | P g} :=
    {| equiv := fun f f' => proj1_sig f == proj1_sig f' |}.
  Proof.
    split.
      intro x; reflexivity.
      intros x y xEy; symmetry; assumption.
      intros x y z xEy yEz; transitivity (proj1_sig y); assumption.
  Defined.

  Instance Perm_Monoid {C : Category} (X : Obj) (P : Aut X -> Prop)
    (Pone : P one) (Pcomp : forall f g, P f -> P g -> P (aut_comp f g))
    : Monoid {g : Aut X | P g} :=
    {| mul := fun f g => exist _ (aut_comp (proj1_sig f) (proj1_sig g))
                               (Pcomp _ _ (proj2_sig f) (proj2_sig g))
     ; one := exist _ (existT _ ident (exist _ ident ident_inverse)) Pone |}.
  Proof.
    intros m1 m2 m3; destruct m1, m2, m3; simpl; split; [symmetry |]; apply comp_assoc.
    intro m; simpl; split; [apply ident_left_unit | apply ident_right_unit].
    intro m; simpl; split; [apply ident_right_unit | apply ident_left_unit].
  Defined.

  Instance Perm_Group {C : Category} (X : Obj) (P : Aut X -> Prop)
    (Pone : P one)
    (Pcomp : forall f g, P f -> P g -> P (aut_comp f g))
    (Pinv : forall f, P f -> P (aut_inv f))
    : Group (H0:=Perm_Monoid X P Pone Pcomp) {g : Aut X | P g} :=
    {| inv := fun f => exist _ (aut_inv (proj1_sig f)) (Pinv _ (proj2_sig f)) |}.
  Proof.
    intros f; destruct f; destruct x; destruct s; destruct i; simpl; split; assumption.
  Defined.

  Definition GroupHom {G H : Set} `{GG : Group G} `{GH : Group H} (h : G -> H) : Prop :=
    MonHom h /\ forall g : G, h (inv g) == inv (h g).
  Definition GroupIso {G H : Set} `{GG : Group G} `{GH : Group H} (h : G -> H) : Prop :=
    GroupHom h /\ exists hi : H -> G, GroupHom hi /\
                                      (forall x, h (hi x) == x) /\
                                      forall x, hi (h x) == x.

  Theorem Cayley : forall (G : Set) `(Group G), exists H `(Group H) h, GroupIso h.
  Proof.
    intros G H MG GG.
  Qed.
End Monoid.