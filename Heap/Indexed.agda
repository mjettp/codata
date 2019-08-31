open import Level using (_⊔_)

open import Relation.Binary using (Rel; Tri; IsTotalOrder)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Sum using (_⊎_)
open _⊎_
open import Data.Maybe using (Maybe)
open Maybe
open import Data.List using (List; _++_)
open List

module Heap.Indexed
  {k r v} (Key : Set k) {_≤_ : Rel Key r}
  (isTotalOrder : IsTotalOrder _≡_ _≤_)
  (V : Key → Set v) where

open IsTotalOrder isTotalOrder
open import Heap.Key Key isTotalOrder

-- Non empty key indexed heaps
record Heap (bot : Bound) : Set (k ⊔ r ⊔ v) where
  inductive
  constructor Node
  field
    key : Key
    val : V key
    bot<key : bot ≤ᵇ ⟨ key ⟩
    children : List (Heap ⟨ key ⟩)

singleton : ∀ {bot} (key : Key) → V key → {{ bound : bot ≤ᵇ ⟨ key ⟩ }} → Heap bot
singleton key val {{ bot<key }} = Node key val bot<key []

-- An O(1) heap variant of merge from mergesort
infixl 5 _∪_
_∪_ : ∀ {bot} → Heap bot → Heap bot → Heap bot
Node key₁ val₁ bot<key₁ children₁ ∪ Node key₂ val₂ bot<key₂ children₂ with total key₁ key₂
... | inj₁ key₁≤key₂ = Node key₁ val₁ bot<key₁ (Node key₂ val₂ ⟨ key₁≤key₂ ⟩ children₂ ∷ children₁)
... | inj₂ key₁≥key₂ = Node key₂ val₂ bot<key₂ (Node key₁ val₁ ⟨ key₁≥key₂ ⟩ children₁ ∷ children₂)

insert : ∀ {bot} (key : Key) → V key → {{ bound : bot ≤ᵇ ⟨ key ⟩ }} → Heap bot → Heap bot
insert key val heap = singleton key val ∪ heap

record Delete (bot : Bound) : Set (k ⊔ r ⊔ v) where
  constructor Node
  field
    key : Key
    val : V key
    bot<key : bot ≤ᵇ ⟨ key ⟩
    children : Maybe (Heap ⟨ key ⟩)

mergePairs : ∀ {bot} → Heap bot → List (Heap bot) → Heap bot
mergePairs a [] = a
mergePairs a (b ∷ []) = a ∪ b
mergePairs a (b ∷ c ∷ ds) = (a ∪ b) ∪ mergePairs c ds

deleteMin : ∀ {bot} → Heap bot → Delete bot
deleteMin (Node key val bot<key []) = Node key val bot<key nothing
deleteMin (Node key val bot<key (h ∷ hs)) = Node key val bot<key (just (mergePairs h hs))
