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
inductive Gentzen : Set (Bₐ.Formula V) → (Bₐ.Formula V) → Prop
  /-- (IS) Initial sequent. -/
  | init : {α} ⊢ α
  /-- (MR) Monotonicity -/
  | mono (hα : X ⊢ α) (hX : X ⊆ X') : X' ⊢ α
  /-- (∧1) And introduction. -/
  | and₁ (hα : X ⊢ α) (hβ : X ⊢ β) : X ⊢ (α ⋏ β)
  /-- (∧2 left) And elimination into left. -/
  | and₂_left  (hX : X ⊢ α ⋏ β) : X ⊢ α
  /-- (∧2 left) And elimination into right. -/
  | and₂_right (hX : X ⊢ α ⋏ β) : X ⊢ β
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

structure ClosedRel (P : (Set (Bₐ.Formula V)) → Bₐ.Formula V → Prop) where
  init : P {α} α
  mono : P X α → X ⊆ X' → P X' α
  and₁ : P X α → P X β → P X (α ⋏ β)
  and₂_left : P X (α ⋏ β) → P X α
  and₂_right : P X (α ⋏ β) → P X β
  not₁ β : P X α → P X (~α) → P X β
  not₂ : P (X ∪ {α}) β → P (X ∪ {~α}) β → P X β

/--
  Principle of rule induction for Gentzen Sequents.
-/
theorem induction (r : ClosedRel P) (h : X ⊢ α) : P X α := by
  induction h
  case init => exact r.init
  case mono hX hα => exact r.mono hα hX
  case and₁ hα hβ => exact r.and₁ hα hβ
  case and₂_left hX => exact r.and₂_left hX
  case and₂_right hX => exact r.and₂_right hX
  case not₁ β hXα hXnα => exact r.not₁ β hXα hXnα
  case not₂ hXα hXnα => exact r.not₂ hXα hXnα

/-- The soundness of `⊢`. Alternatively, `⊢ ⊆ ⊨`. -/
theorem soundness [Inhabited V] (X : Set (Bₐ.Formula V)): X ⊢ α → X ⊨ α := by
  apply induction
  constructor
  case r.init => simp
  case r.mono =>
    intro X α X' hXα hXX' w hwX'
    exact hXα w (fun x hx => hwX' x (hXX' hx))
  case r.and₁ =>
    intro X α β hα hβ w hw
    simp only [Model.satisfies_and, hα w hw, hβ w hw, and_self]
  case r.and₂_left => exact fun hXαβ w hw => (w.satisfies_and.mp (hXαβ w hw)).left
  case r.and₂_right => exact fun hXαβ w hw => (w.satisfies_and.mp (hXαβ w hw)).right
  case r.not₁ =>
    intro X α β hXα hXnα w hw
    simp only [Satisfies.satisfies, Model.value_not, Bool.not_eq_true'] at hXα hXnα
    have := hXα w hw ▸ hXnα w hw
    contradiction
  case r.not₂ =>
    intro X α β hXα hXnα w hw
    simp only [Satisfies.satisfies] at hXα hXnα
    by_cases hα : w.value α = true
    · suffices : ∀ α' ∈ X ∪ {α}, w.value α' = true
      · exact hXα w this
      intro α' hα'
      refine' Or.elim hα' (fun hα'X => hw α' hα'X) (fun hα'α => _)
      · simp only [Set.mem_singleton_iff.mp hα'α, hα]
    · suffices : ∀ α' ∈ X ∪ {~α}, w.value α' = true
      · exact hXnα w this
      intro α' hα'
      refine' Or.elim hα' (fun hα'X => hw α' hα'X) (fun hα'α => _)
      · simp only [Set.mem_singleton_iff.mp hα'α, Model.value_not, hα, Bool.not_false]

end Gentzen
end Gentzen
