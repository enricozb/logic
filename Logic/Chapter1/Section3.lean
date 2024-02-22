import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Set.Finite
import «Logic».Chapter1.Section2

open Notation

section Satisfiability

class Satisfies (α : Sort _) (β : Sort _) where
  satisfies : α → β → Prop

scoped[Notation] infix:50 " ⊨ " => Satisfies.satisfies
scoped[Notation] infix:50 " ⊭ " => fun a b => ¬ a ⊨ b

instance {S : Signature} [Interpretation S] : Satisfies (Model V) (S.Formula V) where
  satisfies w α := w.value α

instance {S : Signature} [Interpretation S] : Satisfies (Model V) (Set (S.Formula V)) where
  satisfies w X := ∀ α ∈ X, w ⊨ α

instance {S : Signature} [Interpretation S] : Satisfies (Set (S.Formula V)) (S.Formula V) where
  satisfies X α := ∀ w : Model V, w ⊨ X → w ⊨ α

instance {S : Signature} [Interpretation S] : Satisfies (Set (S.Formula V)) (Set (S.Formula V)) where
  satisfies X Y := ∀ α ∈ Y, X ⊨ α

variable {S : Signature} [Interpretation S] {V : Type _} [B : S.Boolean V]

@[simp] theorem Model.satisfies_formula (w : Model V) {α : S.Formula V} :
    w ⊨ α ↔ w.value α := by
  rfl

@[simp] theorem Model.satisfies_set (w : Model V) (X : Set (S.Formula V)) :
    w ⊨ X ↔ ∀ α ∈ X, w ⊨ α := by
  rfl

@[simp] theorem Model.satisfies_union (w : Model V) {X : Set (S.Formula V)} {α : S.Formula V} :
    w ⊨ X ∪ {α} ↔ w ⊨ X ∧ w ⊨ α := by
  simp only [Satisfies.satisfies, Set.union_singleton, Set.mem_insert_iff, forall_eq_or_imp,
    and_comm]

@[simp] theorem Model.satisfies_not (w : Model V) {α : S.Formula V} :
    w ⊨ ~α ↔ w ⊭ α := by
  simp only [satisfies_formula, value_not, Bool.not_eq_true, Bool.not_eq_true']

@[simp] theorem Model.satisfies_and (w : Model V) {α β : S.Formula V} :
    w ⊨ α ⋏ β ↔ w ⊨ α ∧ w ⊨ β := by
  simp only [satisfies_formula, value_and, Bool.and_eq_true]

@[simp] theorem Model.satisfies_or (w : Model V) {α β : S.Formula V} :
    w ⊨ α ⋎ β ↔ w ⊨ α ∨ w ⊨ β := by
  simp only [satisfies_formula, value_or, Bool.or_eq_true]

@[simp] theorem Signature.Formula.satisfies_formula (X : Set (S.Formula V)) (α : S.Formula V) :
    X ⊨ α ↔ ∀ w : Model V, w ⊨ X → w ⊨ α  := by
  rfl

@[simp] theorem Signature.Formula.satisfies_set (X Y : Set (S.Formula V)) :
    X ⊨ Y ↔ ∀ α ∈ Y, X ⊨ α := by
  rfl

def Signature.Formula.tautology (α : S.Formula V) := ∀ w : Model V, w ⊨ α

def Signature.Formula.contradiction (α : S.Formula V) := ∀ w : Model V, w ⊭ α

example (p : S.Formula V) : (p ⋎ ~p).tautology := by
  intro w
  by_cases hp : w.value p
  · simp only [Model.satisfies_formula, Model.value_or, hp, Bool.true_or]
  · simp only [Model.satisfies_formula, Model.value_or, Model.value_not, hp,
    Bool.not_false, Bool.or_true]

example (p : S.Formula V) : (p ⋏ ~p).contradiction := by
  intro w
  by_cases hp : w.value p
  all_goals
  · simp only [Model.satisfies_formula, Model.value_and, Model.value_not, hp, Bool.not_true,
    Bool.and_false, Bool.false_and, not_false_eq_true]

example (α β : S.Formula V) : ({α, β} : Set _) ⊨ α ⋏ β := by
  simp only [Satisfies.satisfies, Model.value_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, Bool.and_eq_true,
    imp_self, implies_true, forall_eq_or_imp, forall_eq]

example (α β : S.Formula V) : ({α ⋏ β} : Set _) ⊨ ({α, β} : Set _) := by
  simp only [Satisfies.satisfies, Model.value_and, Set.mem_insert_iff, Set.mem_singleton_iff,
    Bool.and_eq_true, forall_eq, and_imp, forall_eq_or_imp, imp_self, implies_true, and_true]
  exact fun _ ha _ => ha

example [Inhabited V] (X : Set (S.Formula V)) (α : S.Formula V) (hX : X ⊨ (⊥ : S.Formula V)) :
    X ⊨ α := by
  simp only [Satisfies.satisfies]
  simp only [Satisfies.satisfies, Model.value_bot, imp_false, not_forall, Bool.not_eq_true,
    exists_prop] at hX
  intro w hw
  have ⟨β, hβmem, hβval⟩ := hX w
  rw [hw β hβmem] at hβval
  contradiction

example (X : Set (S.Formula V)) (α β : S.Formula V) (h₁ : X ∪ {α} ⊨ β) (h₂ : X ∪ {~α} ⊨ β) :
    X ⊨ β := by
  simp only [Satisfies.satisfies]
  intro w hw
  by_cases hα : w ⊨ α
  · exact h₁ w (w.satisfies_union.mpr ⟨hw, hα⟩)
  · exact h₂ w (w.satisfies_union.mpr ⟨hw, w.satisfies_not.mpr hα⟩)

end Satisfiability

section Substitution

structure Substitution (S : Signature) (V : Type _) where
  values : V → S.Formula V

namespace Substitution

variable {S : Signature} [Interpretation S] {V : Type _}

/-- Induced substitution mapping on formulas. -/
def map_formula (σ : Substitution S V) : S.Formula V → S.Formula V
  | .var v => σ.values v
  | .app a s φs => .app a s (fun i => σ.map_formula (φs i))

theorem map_formula_injective : Function.Injective (@map_formula S V) := by
  simp only [Function.Injective]
  intro σ₁ σ₂ h
  have h_values : σ₁.values = σ₂.values := by
    funext v
    have : σ₁.map_formula (.var v) = σ₁.values v := rfl
    rw [← this, h, map_formula]
  calc
  σ₁ = ⟨σ₁.values⟩ := rfl
  _  = ⟨σ₂.values⟩ := by rw [h_values]

/-- Induced substitution mapping on models. -/
def map_model (σ : Substitution S V) : Model V → Model V := fun w =>
  ⟨fun v => w.value (σ.values v)⟩

end Substitution

instance : FunLike (Substitution S V) (S.Formula V) (S.Formula V) :=
  ⟨Substitution.map_formula, Substitution.map_formula_injective⟩

@[simp] theorem Substitution.coe_fun_map_eq (σ : Substitution S V) {α : S.Formula V} :
    σ α = σ.map_formula α := rfl

@[simp] theorem Substitution.map_var (σ : Substitution B V) {v : V} :
    σ (.var v) = σ.values v := rfl

@[simp] theorem Substitution.map_formula_not (σ : Substitution B V) {α : B.Formula V} :
    σ (~α) = ~(σ α) := by
  simp only [Tilde.tilde, coe_fun_map_eq, map_formula, Matrix.cons_val_fin_one,
    Signature.Formula.app.injEq, heq_eq_eq, true_and]
  ext v
  simp only [Matrix.cons_val_fin_one]

@[simp] theorem Substitution.map_formula_and (σ : Substitution B V) {α β : B.Formula V} :
    σ (α ⋏ β) = (σ α) ⋏ (σ β) := by
  have : (fun i => map_formula σ (![α, β] i)) = ![map_formula σ α, map_formula σ β] := by
    ext v
    match v with
    | ⟨0, _⟩ => simp only [Fin.zero_eta, Matrix.cons_val_zero]
    | ⟨1, _⟩ => simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
  simp_rw [Wedge.wedge, coe_fun_map_eq, map_formula, this]

@[simp] theorem Substitution.map_formula_or (σ : Substitution B V) {α β : B.Formula V} :
    σ (α ⋎ β) = (σ α) ⋎ (σ β) := by
  have : (fun i => map_formula σ (![α, β] i)) = ![map_formula σ α, map_formula σ β] := by
    ext v
    match v with
    | ⟨0, _⟩ => simp only [Fin.zero_eta, Matrix.cons_val_zero]
    | ⟨1, _⟩ => simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
  simp_rw [Vee.vee, coe_fun_map_eq, map_formula, this]

theorem Substitution.model_satisfies_iff (σ : Substitution B V) {w : Model V}
    {α : B.Formula V} : w ⊨ σ α ↔ σ.map_model w ⊨ α := by
  induction α using B.induction with
  | var v => simp_rw [map_var, Satisfies.satisfies, map_model, Model.value]
  | not α hi => simp_rw [map_formula_not, Model.satisfies_not, hi]
  | and α β hα hβ => simp_rw [map_formula_and, Model.satisfies_and, hα, hβ]
  | or α β hα hβ => simp_rw [map_formula_or, Model.satisfies_or, hα, hβ]

theorem Substitution.model_satisfies_set_iff (σ : Substitution B V) {w : Model V}
    {X : Set (B.Formula V)} : w ⊨ σ '' X ↔ σ.map_model w ⊨ X := by
  simp only [Model.satisfies_set, Set.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, σ.model_satisfies_iff]

/-- Substitution invariance, names property (S) in the text. e-/
theorem Substitution.invariance
    [Interpretation S] (σ : Substitution B V) {X : Set (B.Formula V)} {α : B.Formula V} :
    X ⊨ α → σ '' X ⊨ σ α := by
  intro hα w hw
  exact σ.model_satisfies_iff.mpr (hα (σ.map_model w) (σ.model_satisfies_set_iff.mp hw))

end Substitution

/--
  Consequence relations.

  > These are relations `⊢` between sets of formulas and formulas of an arbitrary propositional
  > language F that has the properties corresponding to `refl`, `mono`, `trans`, and `invar`. These
  > properties are the starting point for a general and strong theory of logical systems created by
  > Tarski, which underpins nearly all logical systems considered in the literature.

  (Paraphrased from page 20)
-/
class ConsequenceRel {S : Signature} {V : Type _}
    (r : Set (S.Formula V) → S.Formula V → Prop) where
  refl (h : α ∈ X) : r X α
  mono (h₁ : r X α) (h₂ : X ⊆ X') : r X' α
  trans (h₁ : ∀ γ ∈ Y, r X γ) (h₂ : r Y α) : r X α
  invar (σ : Substitution S V) (h : r X α) : r (σ '' X) (σ α)

namespace ConsequenceRel

/--
  Finitary consequence relations require only finitely many formulas for any logical consequence.
-/
class Finitary {S : Signature} (V : Type _)
    (r : Set (S.Formula V) → S.Formula V → Prop) [ConsequenceRel r] where
  fin (h : r X α) : ∃ X₀ ⊆ X, X₀.Finite ∧ r X₀ α

end ConsequenceRel

theorem semantic_deduction_theorem (X : Set (B.Formula V)) (α β : B.Formula V) :
    X ∪ {α} ⊨ β ↔ X ⊨ α ⟶ β := by
  apply Iff.intro
  · intro h w hwX
    simp only [Arrow.arrow, Satisfies.satisfies, Model.value_not, Model.value_and, Bool.not_and]
    by_cases hα : w ⊨ α
    · have hwβ : w ⊨ β := h w (w.satisfies_union.mpr ⟨hwX, hα⟩)
      simp only [Satisfies.satisfies] at hwβ
      simp only [hwβ, Bool.not_true, Bool.not_false, Bool.or_true]
    · simp only [Satisfies.satisfies, Bool.not_eq_true] at hα
      simp only [hα, Bool.not_false, Bool.true_or]
  · intro h w hwXα
    have ⟨hwX, hwα⟩ := w.satisfies_union.mp hwXα
    have hwXαβ := h w hwX
    simp only [Arrow.arrow, Satisfies.satisfies, Model.value_not, Model.value_and,
      Bool.not_and, Bool.not_not, w.satisfies_formula.mp hwα, Bool.not_true, Bool.false_or] at hwXαβ
    simp only [Model.satisfies_formula, hwXαβ]
