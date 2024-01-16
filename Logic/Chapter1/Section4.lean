import Mathlib.Data.Set.Finite
import «Logic».Chapter1.Section1
import «Logic».Chapter1.Section3

namespace Chapter1
namespace Section4

open Chapter1.Section1 (Signature Interpretation Signature.Formula Model)
open Chapter1.Section1.Notation
open Chapter1.Section3.Notation

inductive Unary | not
inductive Binary | and

/-- The boolean signature `{¬, ∧}`. -/
def 𝓢 : Signature := Signature.mk
  (fun | 1 => Unary | 2 => Binary | _ => Empty)

instance : Interpretation 𝓢 where
  fns := fun {a} => match a with
    | 1 => fun .not b => Bool.not (b 0)
    | 2 => fun .and b => Bool.and (b 0) (b 1)
    | 0 | _+3 => fun _ => by contradiction

instance : Tilde (𝓢.Formula n) := ⟨fun φ => .app 1 .not ![φ]⟩
instance : Wedge (𝓢.Formula n) := ⟨fun φ₁ φ₂ => .app 2 .and ![φ₁, φ₂]⟩
instance : Vee (𝓢.Formula n)   := ⟨fun φ₁ φ₂ => ~(~φ₁ ⋏ ~φ₂)⟩
instance : Bot (𝓢.Formula (n + 1)) := ⟨(.var 0) ⋏ ~(.var 0)⟩
instance : Top (𝓢.Formula (n + 1)) := ⟨~⊥⟩

namespace Calculus

set_option hygiene false
scoped[Chapter1.Section4.Calculus] infix:27 " ⊢ " => Gentzen

/--
  Gentzen Sequents are a relation from sets of formulas to formulas with
  specific construction rules.
-/
inductive Gentzen : Set (𝓢.Formula n) → (𝓢.Formula n) → Prop
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

end Calculus

open Calculus

/- Examples of derivable rules. -/
example : {α, β} ⊢ α ⋏ β := by
  apply Gentzen.and₁
  case' hα => apply Gentzen.mono Gentzen.init
  case' hβ => apply Gentzen.mono Gentzen.init

  all_goals
    simp only [Set.mem_singleton_iff, Set.singleton_subset_iff, Set.mem_insert_iff, true_or, or_true]

lemma true_intro : (∅ : Set (𝓢.Formula (n + 1))) ⊢ ⊤ := by sorry

lemma not_elim (h : X ∪ {~α} ⊢ α) : X ⊢ α := by
  have h₁ : X ∪ {α} ⊢ α
  · have hsub: {α} ⊆ X ∪ {α} := Set.subset_union_right X {α}
    apply Gentzen.mono Gentzen.init hsub
  exact Gentzen.not₂ h₁ h

lemma absurdum (hp : X ∪ {~α} ⊢ β) (hn : X ∪ {~α} ⊢ ~β) : X ⊢ α := by
  have : X ∪ {~α} ⊢ α := Gentzen.not₁ hp hn α
  exact not_elim this

lemma arrow_elim (h : X ⊢ α ⟶ β) : X ∪ {α} ⊢ β := sorry

lemma cut (h₁ : X ⊢ α) (h₂ : X ∪ {α} ⊢ β): X ⊢ β := sorry

lemma arrow_intro (h : X ∪ {α} ⊢ β) : X ⊢ α ⟶ β := sorry

lemma detachment (h₁ : X ⊢ α) (h₂ : X ⊢ α ⟶ β) : X ⊢ β :=
  cut h₁ (arrow_elim h₂)

/--
  Relations that are "closed under Gentzen rules" are relations that relate
  a set of formulas `X` and a formula `α` when the premises are satisfied
  under the relation for some Gentzen rule.

  For example, if some Gentzen rule is of the form "if `X₁ ⊢ α₁, .., Xₙ ⊢ αₙ`,
  then `X ⊢ α`", then `r` is closed under Gentzen rules if
  `r X₁ α₁ ∧ .. ∧ r Xₙ αₙ → r X α`.

  The fields of this class are simply the inductive constructures of `Gentzen`.
-/
class GentzenClosedRel (r : (Set (𝓢.Formula n)) → 𝓢.Formula n → Prop) where
  init : r {α} α
  mono : r X α → X ⊆ X' → r X' α
  and₁ : r X α → r X β → r X (α ⋏ β)
  and₂_left : r X (α ⋏ β) → r X α
  and₂_right : r X (α ⋏ β) → r X β
  not₁ : r X α → r X (~α) → r X β
  not₂ : r (X ∪ {α}) β → r (X ∪ {~α}) β → r X β

/--
  A Gentzen closed relation is implied by the Gentzen derivability relation.
-/
theorem principle_of_rule_induction (G : GentzenClosedRel r) : X ⊢ α → r X α := by
  intro h
  induction h
  case init => exact G.init
  case mono hX hXα => exact G.mono hXα hX
  case and₁ hα hβ => exact G.and₁ hα hβ
  case and₂_left hαβ => exact G.and₂_left hαβ
  case and₂_right hαβ => exact G.and₂_right hαβ
  case not₁ hp hn => exact G.not₁ hp hn
  case not₂ hp hn => exact G.not₂ hp hn

/-- The logical consequence relation `X ⊨ α` is closed under Gentzen rules. -/
instance : GentzenClosedRel (· ⊨ · : Set (𝓢.Formula n) → 𝓢.Formula n → Prop) where
  init := by intro α; simp [Satisfies.satisfies]
  mono := by
    intro X α X' hXα hX w hwX'
    have hwX : w ⊨ X := by intro φ hφ; exact hwX' φ (hX hφ)
    exact hXα w hwX
  and₁ := by
    intro X α β hXα hXβ w hwX
    simp [Satisfies.satisfies, Model.value, Interpretation.fns]
    exact ⟨hXα w hwX, hXβ w hwX⟩
  and₂_left := by
    intro X α β hXαβ w hwX
    simp [Satisfies.satisfies, Model.value, Interpretation.fns] at hXαβ
    exact (hXαβ w hwX).left
  and₂_right := by
    intro X α β hXαβ w hwX
    simp [Satisfies.satisfies, Model.value, Interpretation.fns] at hXαβ
    exact (hXαβ w hwX).right
  not₁ := by
    intro X α β hp hn w hwX
    simp [Satisfies.satisfies, Model.value, Interpretation.fns] at hp hn
    have hαp : w.value α = true := hp w hwX
    have hαn : w.value α = false := hn w hwX
    rw [hαp] at hαn
    contradiction

  not₂ := by
    intro X α β hp hn w hwX
    simp [Satisfies.satisfies] at hp hn
    conv at hn => intro w; simp [Model.value, Interpretation.fns]

    by_cases hα : w.value α = true
    · exact hp w hα hwX
    · simp only [Bool.not_eq_true] at hα
      exact hn w hα hwX

/--
  Theorem 4.1: If `X ⊢ α`, then there is a finite subset `X₀ ⊆ X` such that
  `X₀ ⊢ α`.
-/
theorem finiteness {n : ℕ} {X : Set (𝓢.Formula n)} {α : 𝓢.Formula n}
  (h : X ⊢ α) : ∃ X₀, X₀.Finite ∧ (X₀ ⊆ X) ∧ (X₀ ⊢ α) := by

  let 𝓔 (X : Set (𝓢.Formula n)) α := ∃ X₀, X₀.Finite ∧ (X₀ ⊆ X) ∧ (X₀ ⊢ α)
  suffices : GentzenClosedRel 𝓔
  · exact principle_of_rule_induction this h

  constructor
  case init =>
    intro α
    exact ⟨{α}, Set.finite_singleton α, Set.singleton_subset_singleton.mpr rfl, .init⟩

  case mono =>
    intro X α X' ⟨X₀, hX₀fin, hX₀sub, hX₀α⟩ hX
    exact ⟨X₀, hX₀fin, Set.Subset.trans hX₀sub hX, hX₀α⟩

  case and₁ =>
    intro X α β ⟨X₀, hX₀fin, hX₀sub, hX₀α⟩ ⟨X₁, hX₁fin, hX₁sub, hX₁β⟩
    exact ⟨
      (X₀ ∪ X₁),
      (Set.Finite.union hX₀fin hX₁fin),
      Set.union_subset hX₀sub hX₁sub,
      Gentzen.and₁
        (Gentzen.mono hX₀α (Set.subset_union_left X₀ X₁))
        (Gentzen.mono hX₁β (Set.subset_union_right X₀ X₁))
    ⟩

  sorry
  sorry
  sorry
  sorry


/--
  The soundness theorem states that if a formula `α` can be proved from `X`,
  then it is a logical consequence of `X`. That is, _proofs are sound_.
-/
theorem soundness {n : ℕ} {X : Set (𝓢.Formula n)} {α : 𝓢.Formula n} (hX : X ⊢ α) : X ⊨ α := by
  apply principle_of_rule_induction ?G hX

  -- TODO: this is sensitive to how the instance is named.
  exact instGentzenClosedRelSetFormula𝓢SatisfiesInstSatisfiesSetFormulaInstInterpretation𝓢

end Section4
end Chapter1
