import «Logic».Chapter1.Section2

open Notation

section Satisfiability

class Satisfies (α : Sort _) (β : Sort _) where
  satisfies : α → β → Prop

scoped[Notation] infix:50 " ⊨ " => Satisfies.satisfies
scoped[Notation] infix:50 " ⊭ " => fun a b => ¬(a ⊨ b)

instance {S : Signature} [Interpretation S] : Satisfies (Model V) (S.Formula V) where
  satisfies w α := w.value α

instance {S : Signature} [Interpretation S] : Satisfies (Model V) (Set (S.Formula V)) where
  satisfies w X := ∀ α ∈ X, w ⊨ α

instance {S : Signature} [Interpretation S] : Satisfies (Set (S.Formula V)) (S.Formula V) where
  satisfies X α := ∀ w : Model V, w ⊨ X → w ⊨ α

instance {S : Signature} [Interpretation S] : Satisfies (Set (S.Formula V)) (Set (S.Formula V)) where
  satisfies X Y := ∀ α ∈ Y, X ⊨ α

variable {S : Signature} [Interpretation S]

@[simp] theorem Model.satisfies_formula (w : Model V) (α : S.Formula V) :
    w ⊨ α ↔ w.value α := by
  rfl

@[simp] theorem Model.satisfies_set (w : Model V) (X : Set (S.Formula V)) :
    w ⊨ X ↔ ∀ α ∈ X, w ⊨ α := by
  rfl

@[simp] theorem Model.satisfies_union (w : Model V) {X : Set (S.Formula V)} {α : S.Formula V} :
    w ⊨ X ∪ {α} ↔ w ⊨ X ∧ w ⊨ α := by
  simp only [Satisfies.satisfies, Set.union_singleton, Set.mem_insert_iff, forall_eq_or_imp,
    and_comm]

@[simp] theorem Model.not_satisfies_formula (w : Model V) {α : B.Formula V} :
    w ⊭ α ↔ w ⊨ ~α := by
  simp only [satisfies_formula, value_not, Bool.not_eq_true, Bool.not_eq_true']

@[simp] theorem Signature.Formula.satisfies_formula (X : Set (S.Formula V)) (α : S.Formula V) :
    X ⊨ α ↔ ∀ w : Model V, w ⊨ X → w ⊨ α  := by
  rfl

@[simp] theorem Signature.Formula.satisfies_set (X Y : Set (S.Formula V)) :
    X ⊨ Y ↔ ∀ α ∈ Y, X ⊨ α := by
  rfl

def Signature.Formula.tautology (α : S.Formula V) := ∀ w : Model V, w ⊨ α

def Signature.Formula.contradiction (α : S.Formula V) := ∀ w : Model V, w ⊭ α

example (p : B.Formula V) : (p ⋎ ~p).tautology := by
  intro w
  by_cases hp : w.value p
  · simp only [Model.satisfies_formula, Model.value_or, hp, Bool.true_or]
  · simp only [Model.satisfies_formula, Model.value_or, Model.value_not, hp,
    Bool.not_false, Bool.or_true]

example (p : B.Formula V) : (p ⋏ ~p).contradiction := by
  intro w
  by_cases hp : w.value p
  all_goals
  · simp only [Model.satisfies_formula, Model.value_and, Model.value_not, hp, Bool.not_true,
    Bool.and_false, Bool.false_and, not_false_eq_true]

example (α β : B.Formula V) : ({α, β} : Set _) ⊨ α ⋏ β := by
  simp only [Satisfies.satisfies, Model.value_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, Bool.and_eq_true,
    imp_self, implies_true, forall_eq_or_imp, forall_eq]

example (α β : B.Formula V) : ({α ⋏ β} : Set _) ⊨ ({α, β} : Set _) := by
  simp only [Satisfies.satisfies, Model.value_and, Set.mem_insert_iff, Set.mem_singleton_iff,
    Bool.and_eq_true, forall_eq, and_imp, forall_eq_or_imp, imp_self, implies_true, and_true]
  exact fun _ ha _ => ha

example [Inhabited V] (X : Set (B.Formula V)) (α : B.Formula V) (hX : X ⊨ (⊥ : B.Formula V)) :
    X ⊨ α := by
  simp only [Satisfies.satisfies]
  simp only [Satisfies.satisfies, Model.value_bot, imp_false, not_forall, Bool.not_eq_true,
    exists_prop] at hX
  intro w hw
  have ⟨β, hβmem, hβval⟩ := hX w
  rw [hw β hβmem] at hβval
  contradiction

example (X : Set (B.Formula V)) (α β : B.Formula V) (h₁ : X ∪ {α} ⊨ β) (h₂ : X ∪ {~α} ⊨ β) :
    X ⊨ β := by
  simp only [Satisfies.satisfies]
  intro w hw
  by_cases hα : w ⊨ α
  · exact h₁ w (w.satisfies_union.mpr ⟨hw, hα⟩)
  · exact h₂ w (w.satisfies_union.mpr ⟨hw, w.not_satisfies_formula.mp hα⟩)

end Satisfiability
