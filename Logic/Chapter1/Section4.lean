import Mathlib.Data.Set.Basic
import «Logic».Chapter1.Section3

open Notation

section Gentzen

set_option hygiene false
scoped[Notation] infix:27 " ⊢ " => Gentzen
scoped[Notation] infix:27 " ⊬ " => fun X α => ¬ Gentzen X α

/--
  Gentzen Sequents is a relation from sets of formulas to formulas with specific construction rules.

  The choice of signature `Bₐ = {¬, ∧}` is for convenience as it has few symbols and is functional
  complete.
-/
inductive Gentzen : Set (Bₐ.Formula n) → (Bₐ.Formula n) → Prop
  /-- (IS) Initial sequent. -/
  | init : {α} ⊢ α
  /-- (MR) Monotonicity -/
  | mono (hα : X ⊢ α) (hX : X ⊆ X') : X' ⊢ α
  /-- (∧1) And introduction. -/
  | and₁ (hα : X ⊢ α) (hβ : X ⊢ β) : X ⊢ (α ⋏ β)
  /-- (∧2 left) And elimination into left. -/
  | and₂_left  (hα : X ⊢ α ⋏ β) : X ⊢ α
  /-- (∧2 left) And elimination into right. -/
  | and₂_right (hα : X ⊢ α ⋏ β) : X ⊢ β
  /-- (¬1) -/
  | not₁ (h₁ : X ⊢ α) (h₂ : X ⊢ ~α) β : X ⊢ β
  /-- (¬2) -/
  | not₂ (h₁ : X ∪ {α} ⊢ β) (h₂ : X ∪ {~α} ⊢ β) : X ⊢ β

namespace Gentzen

theorem union_singleton_right : X ∪ {α} ⊢ α := mono init (Set.subset_union_right X {α})

theorem union_singleton_left : {α} ∪ X ⊢ α := mono init (Set.subset_union_left {α} X)

theorem not_elim (h : X ∪ {~α} ⊢ α) : X ⊢ α := not₂ union_singleton_right h

theorem absurd (h₁ : X ∪ {~α} ⊢ β) (h₂ : X ∪ {~α} ⊢ ~β) : X ⊢ α := not_elim (not₁ h₁ h₂ α)

theorem cut (h₁ : X ⊢ α) (h₂ : X ∪ {α} ⊢ β) : X ⊢ β :=
  not₂ h₂ (not₁ (mono h₁ (Set.subset_union_left _ {~α})) union_singleton_right β)

theorem arrow_elim (h : X ⊢ α ⟶ β) : X ∪ {α} ⊢ β := by
  apply not_elim
  · apply not₁
    · apply and₁
      rw [Set.union_comm, ← Set.union_assoc]
      exact union_singleton_right
      exact union_singleton_right
    · rw [Set.union_assoc]
      exact mono h (Set.subset_union_left _ _)

theorem arrow_intro (h : X ∪ {α} ⊢ β) : X ⊢ α ⟶ β := by
  have h1 : X ∪ {α ⋏ ~β} ∪ {α} ⊢ β := by
    rw [Set.union_assoc, Set.union_comm _ {α}, ← Set.union_assoc]
    exact mono h (Set.subset_union_left _ _)
  have h2 : X ∪ {α ⋏ ~β} ⊢ α := and₂_left union_singleton_right
  have h3 : X ∪ {α ⋏ ~β} ⊢ β := cut h2 h1
  have h4 : X ∪ {α ⋏ ~β} ⊢ ~β := and₂_right union_singleton_right
  have h5 : X ∪ {α ⋏ ~β} ⊢ α ⟶ β := not₁ h3 h4 _
  have h6 : X ∪ {~(α ⋏ ~β)} ⊢ α ⟶ β := union_singleton_right
  exact not₂ h5 h6

theorem detachment (h₁ : X ⊢ α) (h₂ : X ⊢ α ⟶ β) : X ⊢ β := cut h₁ (arrow_elim h₂)

end Gentzen
end Gentzen
