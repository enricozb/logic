import «Logic».Chapter1.Section1

namespace Chapter1
namespace Section2

open Chapter1.Section1
open Chapter1.Section1.Notation

/--
  Two formulas (of possibly different signatures) are semantically equivalent
  if they have the same valuation for all models.
-/
@[simp, reducible]
def semantically_equivalent
  {S₁ S₂: Signature} [Interpretation S₁] [Interpretation S₂]
  (φ₁ : S₁.Formula n) (φ₂ : S₂.Formula n) :=
  ∀ w : Model n, w.value φ₁ = w.value φ₂

scoped[Chapter1.Section2] infixr:67 " ≡ " => semantically_equivalent

theorem id (φ : 𝓑.Formula n) : φ ≡ φ := by
  simp only [semantically_equivalent, implies_true]

theorem double_neg (φ : 𝓑.Formula n) : φ ≡ ~~φ := by
  simp only [semantically_equivalent]
  intro w
  simp only [
    Model.value, Interpretation.fns, Bool.not_not,
    Matrix.cons_val_fin_one -- needed for a fin tuple lemma
  ]

/--
  `≡` is an equivalence relation when comparing formulas of the same signature.
-/
instance {n : ℕ} {S: Signature} [Interpretation S] :
  Equivalence (@semantically_equivalent n S S _ _) where
  refl := by simp only [semantically_equivalent, implies_true]
  symm := by
    intro φ₁ φ₂ h w
    exact (h w).symm
  trans := by
    intro φ₁ φ₂ φ₃ h₁ h₂ w
    rw [h₁ w, h₂ w]

/-- `≡` is a _congruence relation_ in `𝓑`. -/
theorem equiv_congr (α α' β β' : 𝓑.Formula n) (hα : α ≡ α') (hβ : β ≡ β') :
  (α ⋏ β ≡ α' ⋏ β') ∧ (α ⋎ β ≡ α' ⋎ β') ∧ (~α ≡ ~α') := by
  apply And.intro; swap; apply And.intro
  all_goals {
    intro w
    simp only [
      Model.value, Interpretation.fns, hα, hβ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ]
  }

/-- Substitutes instances of `α` with `β` in `φ`. -/
def subst {S : Signature} [DecidableEq (S.Formula n)] (α β φ : S.Formula n) : S.Formula n :=
  if φ = α then
    β
  else
    match φ with
    | .var i => .var i
    | .app a s φs => .app a s (fun i => subst α β (φs i))

/--
  Substituting semantically equivalent formulas `α β` within a formula `φ`
  produces an equivalent formula.
-/
theorem replacement
  {S : Signature} [DecidableEq (S.Formula n)] [Interpretation S]
  {φ α β: S.Formula n} (h : α ≡ β) : φ ≡ (subst α β φ) := by
  intro w
  unfold subst
  by_cases hφ : (φ = α)
  · rw [hφ, h w, if_pos rfl]
  · rw [if_neg hφ]
    induction' φ with i a s φs φs_ih
    · rfl
    · simp only [Model.value, Interpretation.fns]
      have φs_ih : ∀ i : Fin a, w.value (φs i) = w.value (subst α β (φs i)) := by
        intro i
        unfold subst
        by_cases hφs : φs i = α
        · rw [hφs, if_pos rfl]
          exact h w
        · rw [if_neg hφs]
          exact φs_ih i hφs
      conv => lhs; arg 2; intro i; rw [φs_ih i]

end Section2
end Chapter1
