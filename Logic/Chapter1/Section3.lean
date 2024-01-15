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
  satisfies (w : Model n) (X : Set (S.Formula n)) := ∀ φ ∈ X, w ⊨ φ

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
  (hsat : X ⊨ φ) (hsub : X ⊆ X') : X' ⊨ φ := by
  intro w hw
  suffices hX : w ⊨ X
  · exact hsat w hX
  intro φ hφ
  exact hw φ (hsub hφ)

/-- Logical consequences are transitive over sets. -/
-- TODO: `φ` here could also be set of formulas `Z`.
theorem trans_logical_consequence {X Y : Set (S.Formula n)} {φ : S.Formula n}
  (h₁ : X ⊨ Y) (h₂ : Y ⊨ φ) : X ⊨ φ := by
  intro w hw
  have : w ⊨ Y := fun ψ hψ => h₁ ψ hψ w hw
  exact h₂ w this

/-- A _substitution_, mapping variables to formulas. -/
-- TODO: substitutions should be specific to `𝓑` it seems.
structure Substitution (n m : ℕ) (S : Signature) where
  map : Fin n → S.Formula m

/-- An extension of a substitution `σ` mapping formulas to formulas. -/
def Substitution.map_formula (σ : Substitution n m S) (φ : S.Formula n) : S.Formula m :=
  match φ with
  | .var i => σ.map i
  | .app a s φs => .app a s (fun i => σ.map_formula (φs i))

scoped[Chapter1.Section3] infixr:69 "ᶠ " => Substitution.map_formula

/-- An extension of a substitution `σ` mapping sets of formulas to sets of formulas. -/
def Substitution.map_set (σ : Substitution n m S) (X : Set (S.Formula n)) : Set (S.Formula m) :=
  {σᶠ φ | φ ∈ X}

scoped[Chapter1.Section3] infixr:69 "ˣ " => Substitution.map_set

/--
  An extension of a substitution `σ` mapping models to models. This is defined
  as the substitution that satisfies `(σ w) φ = w (σ φ)`.

  Note that while `σᶠ` maps `Formula n → Formula m`, `σʷ` maps
  `Model m → Model n` (note the swapping of `n` and `m`).
-/
def Substitution.map_model (σ : Substitution n m S) (w : Model m) : Model n :=
  ⟨fun i => w.value (σᶠ (.var i))⟩

scoped[Chapter1.Section3] infixr:69 "ʷ " => Substitution.map_model

/-- A useful relationship between models and formulas under substitutions. -/
lemma substitution_satisfies (σ : Substitution n m 𝓑) (w : Model m) (φ : 𝓑.Formula n) :
  w ⊨ σᶠ φ ↔ σʷ w ⊨ φ := by
  induction' φ with i a s φs φs_ih
  · rfl
  · match a with
    | 1 => match s with
      | .not =>
        simp only [Satisfies.satisfies, Model.value, Interpretation.fns, Bool.not_eq_true']
        have hφs₀ := Iff.not (φs_ih 0)
        simp [Satisfies.satisfies, Bool.not_eq_true] at hφs₀
        exact hφs₀
    | 2 => match s with
      | .or =>
        simp only [Satisfies.satisfies, Model.value, Interpretation.fns, Bool.or_eq_true]
        have hφs := Iff.or (φs_ih 0) (φs_ih 1)
        simp [Satisfies.satisfies] at hφs
        exact hφs
      | .and =>
        simp only [Satisfies.satisfies, Model.value, Interpretation.fns, Bool.and_eq_true]
        have hφs := Iff.and (φs_ih 0) (φs_ih 1)
        simp [Satisfies.satisfies] at hφs
        exact hφs

/-- Logical consequences are invariant under substitutions. -/
theorem substitution_invariance (σ : Substitution n m 𝓑)
  (X : Set (𝓑.Formula n)) (φ : 𝓑.Formula n) (hX : X ⊨ φ) : σˣ X ⊨ σᶠ φ := by
    intro w hw
    have hσwX : σʷ w ⊨ X := by
      intro ψ hψ
      apply (substitution_satisfies σ w ψ).mp
      apply hw (σᶠ ψ)
      exact ⟨ψ, hψ, rfl⟩

    have hσwφ : σʷ w ⊨ φ := hX (σ.map_model w) hσwX
    exact (substitution_satisfies σ w φ).mpr hσwφ

/--
  The (semantic) deduction theorem for propositional logic: `X, α ⊨ β ↔ X ⊨ α → β`.
-/
theorem deduction_theorem (X : Set (𝓑.Formula n)) (α β : 𝓑.Formula n) :
  (X ∪ {α}) ⊨ β ↔ X ⊨ (α ⟶ β) := by
  apply Iff.intro
  · intro h w hw
    simp only [Satisfies.satisfies, Model.value, Interpretation.fns, Bool.or_eq_true, Bool.not_eq_true']
    by_cases hα : w.value α = true
    · suffices hw' : w ⊨ (X ∪ {α})
      · exact Or.inr (h w hw')
      simp only [Satisfies.satisfies, Set.union_singleton, Set.mem_insert_iff, forall_eq_or_imp]
      exact ⟨hα, hw⟩
    · rw [Bool.not_eq_true] at hα
      exact Or.inl hα

  · intro h w hw
    have h := h w
    simp [Satisfies.satisfies, Model.value, Interpretation.fns, Arrow.arrow] at h
    simp [Satisfies.satisfies] at hw
    have ⟨hα, hX⟩ := hw
    apply Or.elim (h hX)
    · intro hα'; rw [hα] at hα'; contradiction
    · exact id

namespace Exercises

/-- Exercise 3. The rule of disjunctive case distinction. -/
theorem disjunctive_case_distinction (X : Set (𝓑.Formula n)) (α β γ : 𝓑.Formula n)
  (hα : (X ∪ {α}) ⊨ γ) (hβ : (X ∪ {β}) ⊨ γ) : (X ∪ {α ⋎ β}) ⊨ γ := by
  sorry

/--
  A consequence relation, typically denoted `⊢`, is a relation of sets of
  formulas and formulas of a signature with the following properties:

  - _reflexivity_: `α ∈ X → X ⊢ α`.
  - _monotonicity_: `X ⊢ α → X ⊆ X' → X' ⊢ α`.
  - _transitivity_: `X ⊢ Y → Y ⊢ α → X ⊢ α`.
-/
class ConsequenceRel {S : Signature} (r : ∀ {n}, Set (S.Formula n) → S.Formula n → Prop) where
  /-- Reflexivity -/
  refl {n} (X : Set (S.Formula n)) (α : S.Formula n) : α ∈ X → r X α
  /-- Monotonicity -/
  mono {n} (X X' : Set (S.Formula n)) (α : S.Formula n) : r X α → X ⊆ X' → r X' α
  /-- Transitivity -/
  trans {n} (X Y : Set (S.Formula n)) (α : S.Formula n) : (∀ β ∈ Y, r X β) → r Y α → r X α

class HasConsequenceRel (S : Signature) where
  rel : ∀ {n}, Set (S.Formula n) → S.Formula n → Prop
  consequence : ConsequenceRel rel

abbrev HasConsequenceRel.not_rel [C : HasConsequenceRel S] (X : Set (S.Formula n)) (α : S.Formula n) : Prop :=
  ¬(C.rel X α)

scoped[Chapter1.Section3.Exercises] infixr:67 " ⊢ " => HasConsequenceRel.rel
scoped[Chapter1.Section3.Exercises] infixr:67 " ⊬ " => HasConsequenceRel.not_rel

/--
  A set of formulas is consistent if there is some formula that is not a
  consequence. This is because if `X` is inconsistent then `X ⊢ ⊥`, which
  implies `X ⊢ α` for any `α`.
-/
abbrev consistent [HasConsequenceRel S] (X : (Set (S.Formula n))) := ∃ α, X ⊬ α
abbrev inconsistent [HasConsequenceRel S] (X : (Set (S.Formula n))) := ¬ consistent X

/--
  A set of formulas is maximally consistent if any proper extension is
  inconsistent.
-/
abbrev maximally_consistent [HasConsequenceRel S] (X : (Set (S.Formula n))) :=
  consistent X ∧ ∀ α ∉ X, inconsistent (X ∪ {α})

/--
  A set of formulas is deductively closed if it contains all formulas that
  are a consequence of it.
-/
abbrev deductively_closed [HasConsequenceRel S] (X : (Set (S.Formula n))) :=
  ∀ α, X ⊢ α → α ∈ X

/--
  If a set of formulas is maximally consistent, then it is deductively closed.
-/
theorem maximally_consistent_deductively_closed [C : HasConsequenceRel S]
  (X : Set (S.Formula n)) (hX : maximally_consistent X) : deductively_closed X := by
  intro α hα
  apply by_contradiction
  intro hnmem
  suffices hXinc : inconsistent X
  · exact hXinc hX.left

  simp only [not_exists, not_not]
  intro β

  let Y := X ∪ {α}

  have hY : ∀ φ ∈ Y, X ⊢ φ
  · intro φ hφ
    simp only [Set.union_singleton, Set.mem_insert_iff] at hφ
    apply Or.elim hφ
    · intro hφα; rw [hφα]; exact hα
    · intro hφX; exact C.consequence.refl X φ hφX

  have hXαβ : Y ⊢ β
  · have hXαinc := hX.right α hnmem
    simp only [not_exists, not_not] at hXαinc
    exact hXαinc β

  exact C.consequence.trans X Y β hY hXαβ

end Exercises

end Section3
end Chapter1
