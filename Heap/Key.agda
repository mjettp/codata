open import Level using (_⊔_)

open import Relation.Binary using (Rel; IsTotalOrder; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Heap.Key
  {k r} (Key : Set k) {_≤_ : Rel Key r}
  (isTotalOrder : IsTotalOrder _≡_ _≤_) where

open IsTotalOrder isTotalOrder renaming (trans to ≤-trans)

data Bound : Set k where
  -∞  : Bound
  ⟨_⟩ : Key → Bound

data _≤ᵇ_ : Bound → Bound → Set r where
  -∞≤_ : (top : Key) → -∞ ≤ᵇ ⟨ top ⟩
  ⟨_⟩  : ∀ {bot top} → bot ≤ top → ⟨ bot ⟩ ≤ᵇ ⟨ top ⟩

≤ᵇ-trans : Transitive _≤ᵇ_
≤ᵇ-trans {k = ⟨ top ⟩} (-∞≤ bot) ⟨ bot≤top ⟩ = -∞≤ top
≤ᵇ-trans ⟨ bot≤mid ⟩ ⟨ mid≤top ⟩ = ⟨ ≤-trans bot≤mid mid≤top ⟩
