import «Logic».Chapter1.Section2

namespace Chapter1
namespace Section3

open Chapter1.Section1
open Chapter1.Section1.Notation
open Chapter1.Section2

namespace Notation

/-- The definition of the satisfies `⊨` operator. -/
class Satisfies (α : Sort _) (β : Sort _) where
  satisfies : α → β → Prop

def Satisfies.not_satisfies [S : Satisfies α β] (a : α) (b : β) : Prop :=
  ¬(S.satisfies a b)

scoped[Chapter1.Section3.Notation] infixr:67 " ⊨ " => Satisfies.satisfies
scoped[Chapter1.Section3.Notation] infixr:67 " ⊭ " => Satisfies.not_satisfies

/-- A model can satisfy a formula, `w ⊨ φ`. -/
instance {n : ℕ} {S : Signature} [Interpretation S] : Satisfies (Model n) (S.Formula n) where
  satisfies (w : Model n) (φ : S.Formula n) := w.value φ = true

/-- A model can satisfy a set of formulas, `w ⊨ X`. -/
instance {n : ℕ} {S : Signature} [Interpretation S] : Satisfies (Model n) (Set (S.Formula n)) where
  satisfies (w : Model n) (X : Set (S.Formula n)) := ∀ φ ∈ X, w.value φ = true

end Notation

open Notation

variable [Interpretation S] (w : Model n)

/--
  A formula is a tautology if it is satisfied by all models.
-/
def tautology (φ : S.Formula n) : Prop :=
  ∀ (w : Model n), w ⊨ φ

/--
  A formula is a tautology if it is satisfied by no models.
-/
def contradiction (φ : S.Formula n) : Prop :=
  ∀ (w : Model n), w ⊭ φ

/-- An example tautology in `{¬, ∧, ∨}`: `φ(x₀) = x₀ ∨ ¬x₀`. -/
example : tautology ((.var 0) ⋎ ~(.var 0) : 𝓑.Formula 1) := by
  intro w
  simp only [Satisfies.satisfies, Model.value, Interpretation.fns, Bool.or_not_self]

/-- An example tautology in `{¬, ∧, ∨}`: `φ(x₀) = x₀ ∧ ¬x₀`. -/
example : contradiction ((.var 0) ⋏ ~(.var 0) : 𝓑.Formula 1) := by
  intro w
  simp only [
    Satisfies.not_satisfies, Satisfies.satisfies, Model.value, Interpretation.fns,
    Bool.and_not_self, not_false_eq_true
  ]

/--
  A set of formulas can satisfy a single formula, `X ⊨ φ`. This is also called
  a logical consequence.
-/
instance {n : ℕ} {S : Signature} [Interpretation S] : Satisfies (Set (S.Formula n)) (S.Formula n) where
  satisfies (X : Set (S.Formula n)) (φ : S.Formula n) := ∀ (w : Model n), w ⊨ X → w ⊨ φ

/-- The empty set is always satisfied. -/
lemma model_satisfies_empty (w : Model n) : w ⊨ (∅ : Set (S.Formula n)) := by
  intro w
  simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff]

/-- A formula is satisfied by the empty set iff it is a tautology. -/
lemma logical_consequence_iff_tautology (φ : S.Formula n) : (∅ : Set (S.Formula n)) ⊨ φ ↔ tautology φ := by
  apply Iff.intro
  · intro hφ w
    exact hφ w (model_satisfies_empty w)
  · intro hφ w _
    exact hφ w

/--
  A set of formulas can satisfy a set of formulas, `X ⊨ Y`. This is equivalent
  to the statement that all formulas in `Y` are logical consequences of `X`.
-/
instance {n : ℕ} {S : Signature} [Interpretation S] : Satisfies (Set (S.Formula n)) (Set (S.Formula n)) where
  satisfies (X : Set (S.Formula n)) (Y : Set (S.Formula n)) := ∀ y ∈ Y, X ⊨ y

/--
  A formula can satisfy a set of formulas, `φ ⊨ X`. This is just shorthand for
  `{φ} ⊨ X`, defined above.
-/
instance {n : ℕ} {S : Signature} [Interpretation S] : Satisfies (S.Formula n) (Set (S.Formula n)) where
  satisfies (φ : S.Formula n) (X : Set (S.Formula n)) := ({φ} : Set _) ⊨ X

/-- An example of logical consequence, `{α, β} ⊨ α ⋏ β`. -/
example {α β : 𝓑.Formula n} : ({α, β} : Set _) ⊨ (α ⋏ β) := by
  intro w hw
  simp only [Satisfies.satisfies, Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Bool.and_eq_true]
  simp only [Satisfies.satisfies, Set.mem_singleton_iff, Set.mem_insert_iff, forall_eq_or_imp, forall_eq] at hw
  exact hw

/-- An example of logical consequence, `α ⋏ β ⊨ {α, β}`. -/
example {α β : 𝓑.Formula n} : (α ⋏ β) ⊨ ({α, β} : Set _) := by
  intro φ hφ
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hφ
  apply Or.elim hφ
  all_goals {
    intro hφα w hw
    rw [hφα]
    simp [Satisfies.satisfies, Model.value, Interpretation.fns] at hw
    simp only [Satisfies.satisfies]
    try exact hw.left
    try exact hw.right
  }

/-- An example of logical consequence, `{α, α ⟶ β} ⊨ β`. -/
example {α β : 𝓑.Formula n} : ({α, α ⟶ β} : Set _) ⊨ β := by
  intro w hw
  simp [Satisfies.satisfies, Arrow.arrow, Model.value, Interpretation.fns] at hw
  have ⟨hα, himp⟩ := hw
  apply Or.elim himp
  · rw [hα]
    simp only [IsEmpty.forall_iff]
  · exact id

/-- If `X ⊨ ⊥`, then `X ⊨ φ` for any `φ`. -/
example
  {X : Set (𝓑.Formula (n + 1))} (hX : X ⊨ (⊥ : 𝓑.Formula (n + 1)))
  (φ : 𝓑.Formula (n + 1)) : X ⊨ φ := by
  simp [Satisfies.satisfies] at hX
  intro w hw
  have hbot := hX w hw
  simp only [Model.value, Interpretation.fns, Bool.and_not_self] at hbot

/-- If `X ⊨ ⊥`, then no model satisfies `X`. -/
example
  {X : Set (𝓑.Formula (n + 1))} (hX : X ⊨ (⊥ : 𝓑.Formula (n + 1)))
  (w : Model (n + 1)) : w ⊭ X := by
  intro hw
  simp [Satisfies.satisfies] at hX
  have hbot := hX w hw
  simp [Model.value, Interpretation.fns, Bool.and_not_self] at hbot

/--
  Members of a set of formulas are always logical consequences of that set.
  That is, if `φ ∈ X`, then `X ⊨ φ`.
-/
theorem mem_logical_consequence {X : Set (S.Formula n)} {φ : S.Formula n}
  (hmem : φ ∈ X) : X ⊨ φ := by
  intro w hw
  exact hw φ hmem

/-- Logical consequences are preserved under supersets. -/
theorem superset_logical_consequence {X X' : Set (S.Formula n)} {φ : S.Formula n}
  (hmem : φ ∈ X) (hsat : X ⊨ φ) (hsub : X ⊆ X') : X' ⊨ φ := sorry

/-- Logical consequences are transitive over sets. -/
theorem trans_logical_consequence {X Y : Set (S.Formula n)} {φ : S.Formula n}
  (h₁ : X ⊨ Y) (h₂ : Y ⊨ φ) : X ⊨ φ := sorry

end Section3
end Chapter1
