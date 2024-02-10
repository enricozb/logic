import Mathlib.Data.FinEnum
import «Logic».Chapter1_old.Section1

namespace Chapter1
namespace Section2

open Chapter1.Section1
open Chapter1.Section1.Notation

section Utils

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

/-- Negation of boolean tuples. -/
@[simp, reducible]
instance {n : ℕ} : Tilde ([Bool; n]) where
  tilde (b : [Bool; n]) (i : Fin n) := Bool.not (b i)

/-- Negation of boolean functions. -/
@[simp, reducible]
instance {n : ℕ} : Tilde ([Bool; n] → Bool) where
  tilde (f : [Bool; n] → Bool) (b : [Bool; n]) := Bool.not (f b)

/-- Negation of boolean models. -/
@[simp, reducible]
instance {n : ℕ} : Tilde (Model n) where
  tilde (w : Model n) := ⟨~w.vec⟩

end Utils

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
  match satisfying_inputs f with
  | [] => (.var 0) ⋏ ~(.var 0)
  | b::bs' => ⋁ (entry ∘ (b::bs').get)

/--
  Theorem 2.1: Every boolean function of at least one variable is represented
  by its DNF.
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
  let bs := (FinEnum.pi.enum (fun _ => Bool)).filter (~f)

  match h : bs.length with
  | 0 => (.var 0) ⋎ ~(.var 0)
  | l+1 => ⋀ (fun i : Fin (l+1) => entry (bs.get (h ▸ i)))

/--
  Every boolean function of at least one variable is represented by its DNF.
-/
theorem cnf_represents (f : [Bool; n + 1] → Bool) : (cnf f).represents f := by
  sorry

/--
  A signature is _functional complete_ if every boolean function (of at least
  one variable) has a reprentation.

  In keeping with the text, boolean functions of zero variables must be ignored.
  The signature `{¬, ∧, ∨}` cannot represent a boolean function of zero
  variables because formulas of zero variables do not exist, as there are no
  _prime_ formulas.
-/
def Signature.functional_complete (S : Signature) [Interpretation S] :=
  ∀ {n}, ∀ f : [Bool; n + 1] → Bool, ∃ φ : S.Formula (n + 1), φ.represents f

/-- The signature `{¬, ∧, ∨}` is functional complete. -/
theorem 𝓑.functional_complete : Signature.functional_complete 𝓑 := by
  intro n f
  exact ⟨dnf f, dnf_represents f⟩

-- TODO: functional completeness for `{¬, ∧}` and `{¬, ∨}`.

/-- The dual of a boolean formula or boolean function. -/
class Dual (α : Sort _) where
  dual : α → α

instance {n : ℕ} : Dual ([Bool; n] → Bool) where
  dual (f : [Bool; n] → Bool) (b : [Bool; n]) := Bool.not (f (~b))

/-- The dual operator on formulas of signature `{¬, ∧, ∨}`. -/
def 𝓑.dual (φ : 𝓑.Formula n) : 𝓑.Formula n :=
  match φ with
  | .var i => .var i
  | .app 1 s φs => .app 1 s (fun i => 𝓑.dual (φs i))
  | .app 2 .or φs => .app 2 .and (fun i => 𝓑.dual (φs i))
  | .app 2 .and φs => .app 2 .or (fun i => 𝓑.dual (φs i))

instance {n : ℕ} : Dual (𝓑.Formula n) := ⟨𝓑.dual⟩

scoped[Chapter1.Section2] postfix:max "ᵈ" => Dual.dual

/-- The dual operation is its own inverse on formulas. -/
lemma dual_inverse_formula (φ : 𝓑.Formula n) : φᵈᵈ = φ := by
  induction' φ with _ a s φs φs_ih
  · rfl
  · simp only [Dual.dual] at φs_ih
    match a with
    | 1 => match s with
      | .not =>
        simp only [Dual.dual, 𝓑.dual]
        conv => lhs; arg 3; intro i; rw [φs_ih i]
    | 2 => match s with
      | .or =>
        simp only [Dual.dual, 𝓑.dual]
        conv => lhs; arg 3; intro i; rw [φs_ih i]
      | .and =>
        simp only [Dual.dual, 𝓑.dual]
        conv => lhs; arg 3; intro i; rw [φs_ih i]

/-- The dual operation is its own inverse on functions. -/
lemma dual_inverse_function (f : [Bool; n] → Bool) : fᵈᵈ = f := by
  simp only [Dual.dual, instTildeForAllFinBool, Bool.not_not]

/--
  Theorem 2.4: The duality principle for two-valued logic.
-/
theorem duality_principle (φ : 𝓑.Formula n) (hf : φ.represents f) :
  φᵈ.represents fᵈ := by

  rw [Signature.Formula.represents]
  intro w
  induction' φ with _ a s φs φs_ih generalizing f
  · simp only [Dual.dual]
    rw [(by rfl : ~w.vec = (~w).vec), ←hf (~w)]
    simp only [Model.value, instTildeModel, instTildeForAllFinBool, Bool.not_not]
  · match a with
    | 1 => match s with
      | .not =>
        let f₁ := (φs 0).function
        have hf₁ : (φs 0).represents f₁ := (φs 0).represents_function
        have ih := @φs_ih 0 f₁ hf₁
        have hff₁ : ∀ b, f b = Bool.not (f₁ b) := by
          intro bvec
          let b := Model.mk bvec
          rw [(by rfl : bvec = b.vec), ←hf b, ←hf₁ b]
          simp only [Model.value, Interpretation.fns]

        simp only [Model.value, Interpretation.fns]
        conv at ih => lhs; simp only [Dual.dual]
        rw [ih]
        simp only [Dual.dual, Signature.Formula.function]
        rw [(by rfl : ~w.vec = (~w).vec), hf₁ (~w), hff₁]

    | 2 =>
      let f₁ := (φs 0).function
      have hf₁ : (φs 0).represents f₁ := (φs 0).represents_function
      have ih₁ := @φs_ih 0 f₁ hf₁

      let f₂ := (φs 1).function
      have hf₂ : (φs 1).represents f₂ := (φs 1).represents_function
      have ih₂ := @φs_ih 1 f₂ hf₂

      match s with
      | .or =>
        suffices hff₁₂ : ∀ b, f b = Bool.or (f₁ b) (f₂ b)
        · simp only [Model.value, Interpretation.fns]
          conv at ih₁ => lhs; simp only [Dual.dual]
          conv at ih₂ => lhs; simp only [Dual.dual]
          rw [ih₁, ih₂]
          simp only [Dual.dual, Signature.Formula.function]
          rw [(by rfl : ~w.vec = (~w).vec), hf₁ (~w), hf₂ (~w), hff₁₂]
          simp only [Bool.not_or]
        intro bvec
        let b := Model.mk bvec
        rw [(by rfl : bvec = b.vec), ←hf b, ←hf₁ b, ←hf₂ b]
        simp only [Model.value, Interpretation.fns]

      | .and =>
        suffices hff₁₂ : ∀ b, f b = Bool.and (f₁ b) (f₂ b)
        · simp only [Model.value, Interpretation.fns]
          conv at ih₁ => lhs; simp only [Dual.dual]
          conv at ih₂ => lhs; simp only [Dual.dual]
          rw [ih₁, ih₂]
          simp only [Dual.dual, Signature.Formula.function]
          rw [(by rfl : ~w.vec = (~w).vec), hf₁ (~w), hf₂ (~w), hff₁₂]
          simp only [Bool.not_and]
        intro bvec
        let b := Model.mk bvec
        rw [(by rfl : bvec = b.vec), ←hf b, ←hf₁ b, ←hf₂ b]
        simp only [Model.value, Interpretation.fns]


end Section2
end Chapter1
