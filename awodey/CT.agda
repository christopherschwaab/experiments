module CT where
open import Level
open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

postulate extensionality : (a b : Level) → Extensionality a b

record Category c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixr 4 _⇝_ _≈_
  infixr 9 _⊚_
  field
    Obj : Set c
    _⇝_ : Obj → Obj → Set ℓ₁
    _≈_ : ∀{A B} → (A ⇝ B) → (A ⇝ B) → Set ℓ₂
    _⊚_ : ∀{A B C} → (B ⇝ C) → (A ⇝ B) → A ⇝ C
    comp-assoc : ∀{A B C D}{f : C ⇝ D}{g : B ⇝ C}{h : A ⇝ B}
                 → f ⊚ (g ⊚ h) ≈ (f ⊚ g) ⊚ h
    ident : ∀ A → A ⇝ A
    left-unit : ∀{A B} (f : A ⇝ B) → ident B ⊚ f ≈ f
    right-unit : ∀{A B} (f : A ⇝ B) → f ⊚ ident A ≈ f
    
record Functor {c ℓ₁ ℓ₂ d dℓ₁ dℓ₂} (C : Category c ℓ₁ ℓ₂) (D : Category d dℓ₁ dℓ₂)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ d ⊔ dℓ₁ ⊔ dℓ₂) where
  field
    omap : Category.Obj C → Category.Obj D
    fmap : {cd cc : Category.Obj C}{dd dc : Category.Obj D}
         → Category._⇝_ C cd cc → Category._⇝_ D dd dc

posets-category : (c ℓ₁ ℓ₂ : Level) → Category _ _ _
posets-category c ℓ₁ ℓ₂ = record
  { Obj = Poset c ℓ₁ ℓ₂
  ; _⇝_ = λ A B → ∃ (IsMonotone A B)
  ; _≈_ = _≡_
  ; _⊚_ = λ f g → proj₁ f ∘ proj₁ g , λ a a' → proj₂ f _ _ ∘ proj₂ g _ _
  ; comp-assoc = refl
  ; ident = λ A → id , λ a a' a≤a' → a≤a'
  ; left-unit = λ f → refl
  ; right-unit = λ f → refl } where
  IsMonotone : ∀{c ℓ₁ ℓ₂} → (p₁ p₂ : Poset c ℓ₁ ℓ₂) → (Poset.Carrier p₁  → Poset.Carrier p₂) → Set _
  IsMonotone p₁ p₂ m = ∀ a a' → (p₁ Poset.≤ a) a' → (p₂ Poset.≤ m a) (m a')
