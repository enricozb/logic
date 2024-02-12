import Mathlib.Data.FinEnum
import «MathlibExt».Fin
import «Logic».Chapter1.Notation
import «Logic».Chapter1.Section1

open Chapter1.Section1 Notation

namespace Chapter1
namespace Section2

instance : FinEnum Bool := FinEnum.ofList [false, true] (fun b => by
  simp_rw [List.mem_cons, List.not_mem_nil, or_false, Bool.dichotomy])

/- Definition and statements about semantic equivalence of formulas. -/
section SemanticEquivalence

variable {V : Type _} {S : Signature} [Interpretation S]

/--
  Semantic Equivalence: Two formulas (of possibly different signatures) are semantically equivalent
  if they have the same valuation for all models.
-/
abbrev semeq (α β : S.Formula V) :=
  ∀ w : Model V, w.value α = w.value β

scoped infix:67 " ≡ " => semeq

/-- `≡` is an equivalence relation when comparing formulas of the same signature. -/
instance : Equivalence (@semeq V S _) where
  refl := by simp only [semeq, implies_true]
  symm := by intro φ₁ φ₂ h w; exact (h w).symm
  trans := by intro φ₁ φ₂ φ₃ h₁ h₂ w; rw [h₁ w, h₂ w]

theorem semeq_refl {α : S.Formula V} : α ≡ α := instEquivalenceFormulaSemeq.refl α
theorem semeq_symm {α β : S.Formula V} : α ≡ β → β ≡ α := instEquivalenceFormulaSemeq.symm
theorem semeq_trans {α β χ: S.Formula V} : α ≡ β → β ≡ χ → α ≡ χ :=
  instEquivalenceFormulaSemeq.trans

/-- `≡` is a _congruence relation_ in `B`. -/
theorem semeq_congr {α α' β β' : B.Formula V} (hα : α ≡ α') (hβ : β ≡ β') :
    (α ⋏ β ≡ α' ⋏ β') ∧ (α ⋎ β ≡ α' ⋎ β') ∧ (~α ≡ ~α') := by
  refine' ⟨_, _, _⟩
  all_goals simp only [semeq, Model.value, Interpretation.fns, hα, hβ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, implies_true]

/-- Example semantic equivalences for arbitrary propositional variables `V`. -/
example (α β : B.Formula V) :
  α ≡ ~~α ∧
  α ⋏ β ≡ β ⋏ α ∧
  α ⋎ β ≡ β ⋎ α ∧
  α ⋏ α ≡ α ∧
  α ⋎ α ≡ α ∧
  ~(α ⋏ β) ≡ ~α ⋎ ~β ∧
  ~(α ⋎ β) ≡ ~α ⋏ ~β
  := by
  simp only [semeq, Model.value, Interpretation.fns,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Bool.not_not, Bool.not_and, Bool.not_or, Bool.and_comm, Bool.and_self, Bool.or_comm, Bool.or_self,
    implies_true, and_self]

/-- Example semantic equivalences for inhabited propositional variables `V`. -/
example [Inhabited V] (α : B.Formula V) :
  α ⋎ ~α ≡ ⊤ ∧
  α ⋏ ~α ≡ ⊥ ∧
  α ⋏ ⊤  ≡ α ∧
  α ⋎ ⊥  ≡ α
  := by simp only [semeq, Model.value, Interpretation.fns,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Bool.or_not_self, Bool.and_true, Bool.or_false, Bool.and_not_self,
    implies_true, and_self]

variable [DecidableEq (S.Formula V)]

/-- Substitutes instances of `α` with `β` in `φ`. -/
def subst (φ α β : S.Formula V) : S.Formula V :=
  if φ = α then
    β
  else
    match φ with
    | .var p => .var p
    | .app a s φs => .app a s (fun i => subst (φs i) α β)

/-- Notation for substitution. `φ[α ↦ β]` substitutes `α` with `β` in `φ`. -/
scoped notation φ:max "[" α "↦" β "]" => subst φ α β

@[simp] theorem subst_self (α β : S.Formula V) : α[α ↦ β] = β := by
  unfold subst
  simp only [ite_true]

/--
  Substituting semantically equivalent formulas `α β` within a formula `φ`
  produces an equivalent formula.
-/
theorem semeq_of_susbst_semeq (α β φ : S.Formula V) (h : α ≡ β) : φ[α ↦ β] ≡ φ := by
  induction' φ with p a s φs φs_ih
  · by_cases hp : .var p = α
    · rw [subst, if_pos hp, hp]; exact semeq_symm h
    · rw [subst, if_neg hp]; exact semeq_refl

  · by_cases hφs : .app a s φs = α
    · rw [hφs, subst_self]; exact semeq_symm h
    · intro w
      simp only [subst, if_neg hφs, semeq, Model.value, Interpretation.fns, ←φs_ih _ w]

end SemanticEquivalence

section NormalForm

/-- The list of inputs that satisfy `f : 𝔹 n`. -/
def satisfying_inputs (f : 𝔹 n) : List [Bool; n] := (FinEnum.pi.enum (fun _ => Bool)).filter f

theorem mem_satisfying_inputs_iff (f : 𝔹 n) : b ∈ satisfying_inputs f ↔ f b = true := by
  simp only [satisfying_inputs, List.mem_filter, FinEnum.pi.mem_enum, true_and, imp_self]

theorem not_mem_satisfying_inputs_iff (f : 𝔹 n) : b ∉ satisfying_inputs f ↔ f b = false := by
  simp only [mem_satisfying_inputs_iff f, Bool.not_eq_true]

/-- A function `f : 𝔹 n` having no satisfying inputs implies it is false for all inputs. -/
theorem satisfying_inputs_empty_iff (f : 𝔹 n) : satisfying_inputs f = [] ↔ ∀ b, f b = false := by
  apply Iff.intro
  · intro h b
    simp only [← not_mem_satisfying_inputs_iff, h, List.not_mem_nil, not_false_eq_true]
  · intro hf
    simp only [satisfying_inputs, List.filter_eq_nil, hf _, not_false_eq_true, implies_true]

theorem bigand_value (φs : [B.Formula V; n + 1]) (w : Model V) :
    w.value (⋀ φs) = true ↔ ∀ i, w.value (φs i) = true := by
  match n with
  | 0 => simp only [BigWedge.bigwedge, foldop, Fin.forall_fin_one]
  | n + 1 =>
    have bigand_succ {n : ℕ} (φs : [B.Formula V; n + 1 + 1]) :
      ⋀ φs = (⋀ Fin.init φs) ⋏ (φs (Fin.last (n + 1))) := by rfl
    rw [bigand_succ φs]
    simp only [Model.value, Interpretation.fns, bigand_value (Fin.init φs) w, Bool.and_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.init, Fin.forall_fin_succ']

theorem bigor_value (φs : [B.Formula V; n + 1]) (w : Model V) :
    w.value (⋁ φs) = true ↔ ∃ i, w.value (φs i) = true := by
  match n with
  | 0 => simp [BigVee.bigvee, foldop, (@Fin.exists_fin_one fun i => w.value (φs i)).symm]
  | n + 1 =>
    have bigor_succ {n : ℕ} (φs : [B.Formula V; n + 1 + 1]) :
      ⋁ φs = (⋁ Fin.init φs) ⋎ (φs (Fin.last (n + 1))) := by rfl
    rw [bigor_succ φs]
    simp only [Model.value, Interpretation.fns, bigor_value (Fin.init φs) w, Bool.or_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.init, Fin.exists_fin_succ']

def dnf_entry (b : [Bool; n + 1]) : B.Formula (Fin (n + 1)) :=
  (⋀ fun i => if b i then .var i else ~(.var i))

/--
  Disjunctive normal form. The DNF of a boolean function `f : 𝔹 n` is defined only for `n > 0`.
-/
def dnf (f : 𝔹 (n + 1)) : B.Formula (Fin (n + 1)) :=
  let rec dnf' (inputs : List [Bool; n + 1]) :=
    match inputs with
    | [] => ⊥
    | b::bs => (dnf_entry b) ⋎ (dnf' bs)

  dnf' (satisfying_inputs f)

theorem model_value_bot {w : Model _} : w.value (⊥ : B.Formula (Fin (n + 1))) = false := by
  simp only [Model.value, Interpretation.fns, Bool.and_not_self]

theorem model_value_cnf_entry (w : Model _) (b : [Bool; n + 1]) (i : Fin (n + 1)) :
    w.value (if b i = true then (.var i : B.Formula _) else ~(.var i)) = true ↔ w.valuation i = b i := by
  by_cases h : b i = true
  · simp only [h, if_pos h, Model.value]
  · simp only [h, if_neg h, Model.value, Interpretation.fns, Bool.not_eq_true']

theorem model_value_dnf_entry_eq_true_iff_eq (w : Model _) (b : [Bool; n + 1]) :
    w.value (dnf_entry b) = true ↔ w.valuation = b := by
  simp only [dnf_entry, bigand_value, model_value_cnf_entry]
  exact ⟨funext, congrFun⟩

theorem model_value_dnf_eq_true_iff_mem (w : Model _) (bs : List [Bool; n + 1]) :
    w.value (dnf.dnf' bs) = true ↔ w.valuation ∈ bs := by
  match bs with
  | [] => simp only [List.not_mem_nil, iff_false, Bool.not_eq_true, dnf.dnf', model_value_bot]
  | b::bs =>
    simp only [Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Bool.or_eq_true, List.mem_cons]

    refine' ⟨
      fun h => h.elim
        (fun hw => Or.inl ((model_value_dnf_entry_eq_true_iff_eq w b).mp hw))
        (fun hw => Or.inr ((model_value_dnf_eq_true_iff_mem w bs).mp hw)),
      fun h => h.elim
        (fun hw => Or.inl ((model_value_dnf_entry_eq_true_iff_eq w b).mpr hw))
        (fun hw => Or.inr ((model_value_dnf_eq_true_iff_mem w bs).mpr hw))
      ⟩

theorem model_value_dnf_entry_self_eq_true {w : Model (Fin (n + 1))} :
    w.value (dnf_entry w.valuation) = true :=
  (model_value_dnf_entry_eq_true_iff_eq w w.valuation).mpr rfl

/-- Theorem 2.1: Every boolean function of at least one variable is represented by its DNF. -/
theorem dnf_represents (f : 𝔹 (n + 1)) : (dnf f).represents f := by
  intro w

  match h : satisfying_inputs f with
  | [] => simp only [h, dnf, dnf.dnf', model_value_bot, (satisfying_inputs_empty_iff f).mp h]
  | b::bs =>
    simp only [h, dnf, dnf.dnf', Model.value, Interpretation.fns,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

    by_cases hw : w.valuation ∈ satisfying_inputs f
    · rw [(mem_satisfying_inputs_iff f).mp hw]
      apply Or.elim (List.mem_cons.mp (h ▸ hw))
      · intro hwb; simp_rw [← hwb, model_value_dnf_entry_self_eq_true, Bool.true_or]
      · intro hwbs; simp_rw [(model_value_dnf_eq_true_iff_mem w bs).mpr hwbs, Bool.or_true]

    · rw [(not_mem_satisfying_inputs_iff f).mp hw, Bool.or_eq_false_iff]
      rw [h, List.mem_cons.not, not_or] at hw
      have left := (model_value_dnf_entry_eq_true_iff_eq w b).not.mpr hw.left
      have right := (model_value_dnf_eq_true_iff_mem w bs).not.mpr hw.right
      rw [Bool.not_eq_true] at left right

      exact ⟨left, right⟩

end NormalForm

end Section2
end Chapter1
