import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite
import Mathlib.Order.Zorn
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
scoped[Chapter1.Section4.Calculus] infix:27 " ⊬ " => fun X α => ¬ Gentzen X α

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

lemma absurdum₁ (hp : X ∪ {~α} ⊢ β) (hn : X ∪ {~α} ⊢ ~β) : X ⊢ α := by
  have : X ∪ {~α} ⊢ α := Gentzen.not₁ hp hn α
  exact not_elim this

lemma absurdum₂ {X : Set (𝓢.Formula (n + 1))} (hp : X ⊢ ⊥) : X ⊢ α := by
  sorry

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

/--
  A set of formulas is called consistent if there is some formula `α` that
  cannot be proved from it. This is because from an inconsistent `X`, `⊥` can
  be proved, and from `⊥`, anything can be proved.
-/
def consistent (X : Set (𝓢.Formula n)) := ∃ α, X ⊬ α
def inconsistent (X : Set (𝓢.Formula n)) := ¬ consistent X

/--
  A maximally consistent set of formulas is a consistent set where any proper
  extension is inconsistent.
-/
def maximally_consistent (X : Set (𝓢.Formula n)) := consistent X ∧ ∀ α ∉ X, inconsistent (X ∪ {α})

theorem maximally_consistent_iff (X : Set (𝓢.Formula n)) :
  maximally_consistent X ↔ ∀ α, α ∈ X ∨ ~α ∈ X := by sorry

/-- Lemma 4.2a: The derivability relation C⁺. -/
lemma derivable_pos_iff {α : 𝓢.Formula (n + 1)} : X ⊢ α ↔ X ∪ {~α} ⊢ ⊥ := by
  apply Iff.intro
  · intro hXα
    have hXαp : X ∪ {~α} ⊢ α := by
      apply Gentzen.mono hXα
      simp only [Set.union_singleton, Set.subset_insert]

    have hXαn : X ∪ {~α} ⊢ ~α := by
      apply Gentzen.mono Gentzen.init
      simp only [Set.union_singleton, Set.singleton_subset_iff, Set.mem_insert_iff, true_or]

    exact Gentzen.not₁ hXαp hXαn ⊥

  · intro hXnαbot
    have hXnα₁ := Gentzen.and₂_left hXnαbot
    have hXnα₂ := Gentzen.and₂_right hXnαbot
    have hXnαα : X ∪ {~α} ⊢ α := Gentzen.not₁ hXnα₁ hXnα₂ α
    exact not_elim hXnαα

/-- Lemma 4.2b: The derivability relation C⁻. -/
lemma derivable_neg_iff {α : 𝓢.Formula (n + 1)} : X ⊢ ~α ↔ X ∪ {α} ⊢ ⊥ := by
  sorry

/--
  A finite subset of some chain has a maximum set. This lemma is needed for
  Lindenbaum's theorem.
-/
lemma chain_fin_subset_max
  {α : Sort _} {K : Set (Set α)} (hKne : Set.Nonempty K) (hKc : IsChain (· ⊆ ·) K)
  (U₀ : Set α) (hU₀fin : Set.Finite U₀)
  (map : ∀ αᵢ ∈ U₀, ∃ Yᵢ ∈ K, αᵢ ∈ Yᵢ) : ∃ Y ∈ K, U₀ ⊆ Y := by
  induction' h : Set.ncard U₀ with n n_ih generalizing U₀
  · rw [Set.ncard_eq_zero hU₀fin] at h
    rw [h]
    have ⟨Y, hY⟩ := hKne
    exact ⟨Y, hY, Set.empty_subset Y⟩

  · have ⟨αₙ, U₀', hαₙnotin, hαₙinsert, hU₀'card⟩ := Set.eq_insert_of_ncard_eq_succ h
    have hαₙ : αₙ ∈ U₀ := by rw [←hαₙinsert]; exact Set.mem_insert _ _
    have hαₙinsert_sub : insert αₙ U₀' ⊆ U₀ := by rw [hαₙinsert]
    have hU₀'sub : U₀' ⊂ U₀ := Set.ssubset_iff_insert.mpr ⟨αₙ, hαₙnotin, hαₙinsert_sub⟩
    have hU₀'fin : Set.Finite U₀' := Set.Finite.subset hU₀fin hU₀'sub.left
    have map' : ∀ αᵢ ∈ U₀', ∃ Yᵢ ∈ K, αᵢ ∈ Yᵢ := by
      intro αᵢ hαᵢ
      exact map αᵢ (Set.mem_of_subset_of_mem hU₀'sub.left hαᵢ)
    have ⟨Y', hY'memK, hY'sup⟩ := n_ih U₀' hU₀'fin map' hU₀'card
    have ⟨Yₙ, hYₙmemK, hαₙmemYₙ⟩ := map αₙ hαₙ

    wlog hneq : Y' ≠ Yₙ
    · simp only [ne_eq, not_not] at hneq
      apply Exists.intro Y'
      apply And.intro hY'memK
      intro αᵢ hαᵢ
      simp [←hαₙinsert] at hαᵢ
      match hαᵢ with
      | Or.inl hαᵢeqαₙ => rw [hαᵢeqαₙ, hneq]; exact hαₙmemYₙ
      | Or.inr hαᵢmemU₀' => exact hY'sup hαᵢmemU₀'

    apply Or.elim (hKc hY'memK hYₙmemK hneq)
    · intro hY'subYₙ
      suffices hU₀subYₙ : U₀ ⊆ Yₙ
      · exact ⟨Yₙ, hYₙmemK, hU₀subYₙ⟩
      intro αᵢ hαᵢ
      simp [←hαₙinsert] at hαᵢ
      match hαᵢ with
      | Or.inl hαᵢeqαₙ => rw [hαᵢeqαₙ]; exact hαₙmemYₙ
      | Or.inr hαᵢmemU₀' => exact hY'subYₙ (hY'sup hαᵢmemU₀')

    · intro hYₙsub
      apply Exists.intro Y'
      apply And.intro hY'memK
      intro αᵢ hαᵢ
      simp [←hαₙinsert] at hαᵢ
      match hαᵢ with
      | Or.inl hαᵢeqαₙ => rw [hαᵢeqαₙ]; exact hYₙsub hαₙmemYₙ
      | Or.inr hαᵢmemU₀' => exact hY'sup hαᵢmemU₀'

/--
  Lemma 4.3: Lindenbaum's theorem. A consistent set of formulas `X` can be
  extended to a maximually consistent set `X' ⊇ X`.
-/
lemma consistent_maximal_extension {X : Set (𝓢.Formula (n + 1))} (h : consistent X) :
  ∃ X', X ⊆ X' ∧ maximally_consistent X' := by
  let H := {X' | X ⊆ X' ∧ consistent X'}
  have ⟨X', hX'mem, hX'max⟩ : ∃ X' ∈ H, ∀ Y ∈ H, X' ⊆ Y → Y = X' := by
    apply zorn_subset
    intro K hKsub hKchain

    wlog hKnonempty : ∃ Y, Y ∈ K
    · simp only [not_exists] at hKnonempty
      exact ⟨X, ⟨Eq.subset rfl, h⟩, fun Y hY => (hKnonempty Y hY).elim⟩

    let U := ⋃₀ K
    suffices hU : U ∈ H
    · exact ⟨U, hU, fun Y hY => Set.subset_sUnion_of_mem hY⟩

    apply And.intro

    show X ⊆ U
    · intro x hx
      simp only [Set.mem_sUnion]
      have ⟨Y, hY⟩ := hKnonempty
      exact ⟨Y, hY, (hKsub hY).left hx⟩

    show consistent U
    · apply by_contradiction
      simp only [consistent, not_exists, not_not]
      intro hU
      have hUbot : U ⊢ ⊥ := hU ⊥

      have ⟨U₀, hU₀fin, hU₀subU, hU₀bot⟩ := finiteness hUbot
      have map : ∀ αᵢ ∈ U₀, ∃ Yᵢ ∈ K, αᵢ ∈ Yᵢ := by
        intro αᵢ hαᵢ
        exact hU₀subU hαᵢ

      have ⟨Y, hYmem, hYsub⟩ : ∃ Y ∈ K, U₀ ⊆ Y :=
        chain_fin_subset_max hKnonempty hKchain U₀ hU₀fin map

      have hYbot : Y ⊢ ⊥ := Gentzen.mono hU₀bot hYsub
      have hYmemH : Y ∈ H := hKsub hYmem
      have hYcon : consistent Y := hYmemH.right
      have hYinc : inconsistent Y := by
        simp [inconsistent, consistent, not_exists, not_not]
        intro α
        exact absurdum₂ hYbot

      contradiction

  have maximally_consistent_X' : ∀ α ∉ X', inconsistent (X' ∪ {α})
  · intro α hα hαcon
    let Y := X' ∪ {α}
    have hYmem : Y ∈ H := Set.mem_sep (Set.subset_union_of_subset_left (hX'mem.left) {α}) hαcon
    have hαmemY : α ∈ Y := Set.mem_union_right X' rfl
    have hYαsup : X' ⊆ Y := Set.subset_union_left X' {α}
    rw [←(hX'max Y hYmem hYαsup)] at hα
    contradiction

  exact ⟨X', hX'mem.left, hX'mem.right, maximally_consistent_X'⟩

end Section4
end Chapter1
