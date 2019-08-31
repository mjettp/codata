open import Level using (Level; suc)
open import Size using (Size; ∞)

open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Tri; IsStrictTotalOrder)
open Tri
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_)
open _≤_
open import Data.Nat.Properties using (<-isStrictTotalOrder)
open IsStrictTotalOrder <-isStrictTotalOrder
open import Data.Nat.Divisibility using (_∣_; divides)
open import Function using (_∘_)
open import Data.Sum using (_⊎_)
open _⊎_
open import Data.List using (List; []; _∷_)

open import Codata.Thunk using (Thunk; force)
open import Codata.Stream using (Stream; _∷_)
open import Codata.Colist using (Colist; []; _∷_)

module Primality where

postulate
  TODO : ∀ {a} {A : Set a} -> A

auto : ∀ {a} {A : Set a} {{ it : A }} → A
auto {{ it }} = it

module _ {a} {A : Set a} where

  data Finite : Colist A ∞ → Set (suc a) where
    []  : Finite []
    _∷_ : ∀ {xs : Thunk (Colist A) ∞} x → Finite (xs .force) → Finite (x ∷ xs)

  infinite-colist : ∀ {i} (xs : Colist A ∞) → ¬ (Finite xs) → Stream A i
  infinite-colist [] ¬finite = ⊥-elim (¬finite [])
  infinite-colist (x ∷ xs) ¬finite = x ∷ λ where .force → infinite-colist (xs .force) (¬finite ∘ (x ∷_))

  finite-colist : {xs : Colist A ∞} -> Finite xs -> List A
  finite-colist [] = []
  finite-colist (x ∷ xs) = x ∷ finite-colist xs

record IsComposite (n : ℕ) : Set where
  constructor IsComposite✓
  field
    x : ℕ
    y : ℕ
    x<n : x < n
    y<n : y < n
    composite : x * y ≡ n

-- composite? : Decidable IsComposite
-- composite? = {!!}

record IsPrime (p : ℕ) : Set where
  constructor IsPrime✓
  field
    1<p : 1 < p
    primality : ∀ {i} → i ∣ p → 1 ≡ i ⊎ p ≡ i
open IsPrime public

-- 2-IsPrime : IsPrime 2
-- 2-IsPrime = IsPrime✓ 1<2 2-primality
--   where
--   1<2 = s≤s (s≤s z≤n)
--   2-primality : ∀ {i} → i ∣ 2 → 1 ≡ i ⊎ 2 ≡ i

record Prime : Set where
  field
    n : ℕ
    isPrime : IsPrime n

