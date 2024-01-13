import Mathlib.Data.FinEnum
import «Logic».Chapter1.Section1

namespace Chapter1
namespace Section2

open Chapter1.Section1
open Chapter1.Section1.Notation

/-- `Bool` can be finitely enumerated. -/
instance : FinEnum Bool := ⟨
  -- card
  2,
  -- mappings between Bool and Fin 2
  (fun b => if b then 1 else 0),
  (fun i => if i = 0 then false else true),
  -- proofs that above maps are inverses of each other
  (by simp [Function.LeftInverse]),
  (by
    simp [Function.RightInverse, Function.LeftInverse]
    intro x
    by_cases h : x = 0
    · rw [if_pos h]; exact h.symm
    · rw [if_neg h]; exact (Fin.eq_one_of_neq_zero x h).symm
  )
⟩

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
theorem susbst_equiv
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

/-- The list of inputs that satisfy `f`. -/
def satisfying_inputs (f : [Bool; n] → Bool) : List [Bool; n] :=
  (FinEnum.pi.enum (fun _ => Bool)).filter f

/--
  A function having no satisfying inputs implies it is false for all inputs.
-/
lemma satisfying_inputs_empty (f : [Bool; n] → Bool) (hf : (satisfying_inputs f) = []) :
  ∀ b, f b = false := by
  intro b
  apply by_contradiction
  intro hfb
  rw [Bool.not_eq_false] at hfb
  have hb_mem : b ∈ satisfying_inputs f := List.mem_filter.mpr ⟨FinEnum.pi.mem_enum _, hfb⟩
  rw [hf] at hb_mem
  exact List.not_mem_nil b hb_mem

lemma bigand_value (φs : [𝓑.Formula n; a + 1]) (w : Model n) :
  (w.value (⋀ φs) = true) ↔ ∀ i, w.value (φs i) = true := by
    apply Iff.intro

    · intro hw
      induction' a with k k_ih
      · simp only [BigWedge.bigwedge, bigop] at hw
        intro i
        exact (by exact Fin.eq_zero i : i = 1) ▸ hw
      · simp [BigWedge.bigwedge, bigop, Model.value, Interpretation.fns] at hw
        have ⟨hφ, hφs⟩ := hw
        intro i
        match i with
        | ⟨0, _⟩ => exact hφ
        | ⟨i+1, hi⟩ =>
          have htail := k_ih (Fin.tail φs) hφs
          rw [Fin.tail_def] at htail
          exact htail ⟨i, Nat.succ_lt_succ_iff.mp hi⟩

    · sorry

lemma bigor_value (φs : [𝓑.Formula n; a + 1]) (w : Model n) :
  w.value (⋁ φs) = true ↔ ∃ i, w.value (φs i) = true := by sorry

/--
  The disjunctive normal form of a boolean function `f`.
  Disjunctive normal forms do not exist for formulas of zero variables.
-/
def dnf (f : [Bool; n + 1] → Bool) : 𝓑.Formula (n + 1) :=
  /- A cnf of variables. -/
  let entry (b : [Bool; n + 1]) : 𝓑.Formula (n + 1) :=
    ⋀ (fun i => if b i then .var i else ~(.var i))

  /- A list of boolean vectors that satisfy `f`. -/
  let bs := (satisfying_inputs f)

  match bs with
  | [] => (.var 0) ⋏ ~(.var 0)
  | b::bs' => ⋁ (fun i : Fin (bs'.length + 1) => entry ((b::bs').get i))

/--
  Every boolean function of at least one variable is represented by its DNF.
-/
theorem dnf_represents (f : [Bool; n + 1] → Bool) : (dnf f).represents f := by
  rw [Signature.Formula.represents]
  intro w
  simp only [dnf]
  match hsf : satisfying_inputs f with
  | [] =>
    simp only [Model.value, Interpretation.fns, Bool.and_not_self]
    exact (satisfying_inputs_empty f hsf w.vec).symm
  | b::bs =>
    simp only [Model.value]
    by_cases hfw : f w.vec = true
    · rw [hfw]
      apply (bigor_value _ w).mpr
      have hw : w.vec ∈ (b::bs) := by
        rw [←hsf]
        exact List.mem_filter.mpr ⟨FinEnum.pi.mem_enum _, hfw⟩
      have ⟨iw, hiw⟩ := List.mem_iff_get.mp hw
      apply Exists.intro iw
      apply (bigand_value _ w).mpr
      intro i
      by_cases hbi : (b::bs).get iw i = true
      · rw [if_pos hbi, Model.value, ←hiw, hbi]
      · rw [if_neg hbi]
        simp [Model.value, Interpretation.fns]
        rw [←hiw, Bool.eq_false_iff.mpr hbi]
    · rw [Bool.eq_false_iff.mpr hfw, ←Bool.not_eq_true]
      apply (Iff.not (bigor_value _ w)).mpr; rw [not_exists]
      intro iw
      apply (Iff.not (bigand_value _ w)).mpr
      intro hiw
      have hw : w.vec = (b::bs).get iw := by
        funext i
        have := hiw i
        by_cases hiwi : (b::bs).get iw i = true
        · rw [hiwi, if_pos rfl, Model.value] at this
          rw [hiwi, this]
        · simp [if_neg hiwi, Model.value, Interpretation.fns] at this
          rw [Bool.not_eq_true] at hiwi
          rw [hiwi, this]
      have hw_mem : w.vec ∈ (b::bs) := List.mem_iff_get.mpr ⟨iw, hw.symm⟩
      rw [←hsf, satisfying_inputs, List.mem_filter] at hw_mem
      exact hfw hw_mem.right

/--
  The conjunctive normal form of a boolean function `f`.
  Conjunctive normal forms do not exist for formulas of zero variables.
-/
def cnf (f : [Bool; n + 1] → Bool) : 𝓑.Formula (n + 1) :=
  /- A cnf of variables. -/
  let entry (b : [Bool; n + 1]) : 𝓑.Formula (n + 1) :=
    ⋁ (fun i => if b i then ~(.var i) else .var i)

  /- A list of boolean vectors that _do not_ satisfy `f`. -/
  let bs := (FinEnum.pi.enum (fun _ => Bool)).filter (fun b => ¬ f b)

  match h : bs.length with
  | 0 => (.var 0) ⋎ ~(.var 0)
  | l+1 => ⋀ (fun i : Fin (l+1) => entry (bs.get (h ▸ i)))

/--
  Every boolean function of at least one variable is represented by its DNF.
-/
theorem cnf_represents (f : [Bool; n + 1] → Bool) : (cnf f).represents f := by
  sorry

end Section2
end Chapter1
