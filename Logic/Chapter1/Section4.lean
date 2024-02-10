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

lemma mem_provable (h : α ∈ X) : X ⊢ α := by
  have : {α} ⊆ X := Set.singleton_subset_iff.mpr h
  exact Gentzen.mono (Gentzen.init) this

lemma not_elim (h : X ∪ {~α} ⊢ α) : X ⊢ α := by
  have h₁ : X ∪ {α} ⊢ α
  · have hsub: {α} ⊆ X ∪ {α} := Set.subset_union_right X {α}
    apply Gentzen.mono Gentzen.init hsub
  exact Gentzen.not₂ h₁ h

lemma absurdum₁ (hp : X ∪ {~α} ⊢ β) (hn : X ∪ {~α} ⊢ ~β) : X ⊢ α := by
  have : X ∪ {~α} ⊢ α := Gentzen.not₁ hp hn α
  exact not_elim this

lemma absurdum₂ {X : Set (𝓢.Formula (n + 1))} (h : X ⊢ ⊥) : X ⊢ α :=
  Gentzen.not₁ (Gentzen.and₂_left h) (Gentzen.and₂_right h) α

lemma true_intro : (∅ : Set (𝓢.Formula (n + 1))) ⊢ ⊤ := by
  have h₁ : (∅ : Set (𝓢.Formula (n + 1))) ∪ {⊥} ⊢ ⊤ := by
    simp only [Set.union_singleton, insert_emptyc_eq]
    exact absurdum₂ Gentzen.init

  have h₂ : (∅ : Set (𝓢.Formula (n + 1))) ∪ {~⊥} ⊢ ⊤ := by
    exact Gentzen.mono Gentzen.init (Set.subset_union_right ∅ {⊤})

  exact Gentzen.not₂ h₁ h₂

lemma arrow_elim (h : X ⊢ α ⟶ β) : X ∪ {α} ⊢ β := by
  sorry

lemma cut (h₁ : X ⊢ α) (h₂ : X ∪ {α} ⊢ β): X ⊢ β := by
  have hp : X ∪ {~α} ⊢ α := Gentzen.mono h₁ (Set.subset_union_left X {~α})
  have hn : X ∪ {~α} ⊢ ~α := Gentzen.mono Gentzen.init (Set.subset_union_right X {~α})
  have hβ : X ∪ {~α} ⊢ β := Gentzen.not₁ hp hn β

  exact Gentzen.not₂ h₂ hβ

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
  Theorem 4.1: If `X ⊢ α`, then there is a finite subset `X₀ ⊆ X` such that `X₀ ⊢ α`.
-/
theorem finiteness {n : ℕ} {X : Set (𝓢.Formula n)} {α : 𝓢.Formula n}
  (h : X ⊢ α) : ∃ X₀ ⊆ X, X₀.Finite ∧ (X₀ ⊢ α) := by

  let 𝓔 (X : Set (𝓢.Formula n)) α := ∃ X₀ ⊆ X, X₀.Finite ∧ (X₀ ⊢ α)
  suffices : GentzenClosedRel 𝓔
  · exact principle_of_rule_induction this h

  constructor
  case init =>
    intro α
    exact ⟨{α}, Set.singleton_subset_singleton.mpr rfl, Set.finite_singleton α, .init⟩

  case mono =>
    intro X α X' ⟨X₀, hX₀sub, hX₀fin, hX₀α⟩ hX
    exact ⟨X₀, Set.Subset.trans hX₀sub hX, hX₀fin, hX₀α⟩

  case and₁ =>
    intro X α β ⟨X₀, hX₀sub, hX₀fin, hX₀α⟩ ⟨X₁, hX₁sub, hX₁fin, hX₁β⟩
    exact ⟨
      X₀ ∪ X₁,
      Set.union_subset hX₀sub hX₁sub,
      Set.Finite.union hX₀fin hX₁fin,
      Gentzen.and₁
        (Gentzen.mono hX₀α (Set.subset_union_left X₀ X₁))
        (Gentzen.mono hX₁β (Set.subset_union_right X₀ X₁))
    ⟩

  case and₂_left =>
    intro X α β ⟨X₀, hX₀sub, hX₀fin, hX₀αβ⟩
    exact ⟨X₀, hX₀sub, hX₀fin, Gentzen.and₂_left hX₀αβ⟩

  case and₂_right =>
    intro X α β ⟨X₀, hX₀sub, hX₀fin, hX₀αβ⟩
    exact ⟨X₀, hX₀sub, hX₀fin, Gentzen.and₂_right hX₀αβ⟩

  case not₁ =>
    intro X α β ⟨X₀, hX₀sub, hX₀fin, hX₀p⟩ ⟨X₁, hX₁sub, hX₁fin, hX₁n⟩
    exact ⟨
      X₀ ∪ X₁,
      Set.union_subset hX₀sub hX₁sub,
      Set.Finite.union hX₀fin hX₁fin,
      Gentzen.not₁
        (Gentzen.mono hX₀p (Set.subset_union_left X₀ X₁))
        (Gentzen.mono hX₁n (Set.subset_union_right X₀ X₁))
        β
    ⟩

  case not₂ =>
    intro X α β ⟨X₀, hX₀sub, hX₀fin, hX₀p⟩ ⟨X₁, hX₁sub, hX₁fin, hX₁n⟩
    -- need to show that X₀ doesn't have to include α
    -- same with X₁ and ~α
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

lemma consistent₁ (hc : consistent X) (hα : X ⊢ α) : X ⊬ ~α := by
  apply by_contradiction
  intro hnα
  simp only [not_not] at hnα
  have ⟨β, hβ⟩ := hc
  exact hβ (Gentzen.not₁ hα hnα β)

lemma consistent₂ (hc : consistent X) (hnα : X ⊢ ~α) : X ⊬ α := by
  apply by_contradiction
  intro hα
  simp at hα
  have ⟨β, hβ⟩ := hc
  exact hβ (Gentzen.not₁ hα hnα β)

/--
  A maximally consistent set of formulas is a consistent set where any proper
  extension is inconsistent.
-/
def maximally_consistent (X : Set (𝓢.Formula n)) := consistent X ∧ ∀ α ∉ X, inconsistent (X ∪ {α})

lemma maximally_consistent_iff (X : Set (𝓢.Formula n)) :
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
  (map : ∀ aᵢ ∈ U₀, ∃ Yᵢ ∈ K, aᵢ ∈ Yᵢ) : ∃ Y ∈ K, U₀ ⊆ Y := by
  induction U₀, hU₀fin using Set.Finite.dinduction_on with
  | H0 =>
    have ⟨Y, hY⟩ := hKne
    exact ⟨Y, hY, Set.empty_subset _⟩

  | @H1 αₙ U₀' _ _ ih =>
    have ⟨Yₙ, hYₙmemK, hαₙmemYₙ⟩ := map αₙ (Set.mem_insert _ _)
    have ⟨Y', hY'memK, hY'sup⟩ := ih (fun a ha => map a (Set.mem_insert_of_mem _ ha))
    obtain rfl | hne := eq_or_ne Yₙ Y'
    · exact ⟨Yₙ, hYₙmemK, Set.insert_subset hαₙmemYₙ hY'sup⟩
    cases hKc hY'memK hYₙmemK hne.symm with
    | inl h =>
      exact ⟨Yₙ, hYₙmemK, Set.insert_subset hαₙmemYₙ (hY'sup.trans h)⟩
    | inr h =>
      refine ⟨Y', hY'memK, Set.insert_subset (h hαₙmemYₙ) hY'sup⟩

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

      have ⟨U₀, hU₀subU, hU₀fin, hU₀bot⟩ := finiteness hUbot
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

/--
  Lemma 4.4: A maximally consistent set `X` has the property `X ⊢ ¬α ↔ X ⊬ α`,
  for any formula `α`.
-/
lemma maximally_consistent_neg {X : Set (𝓢.Formula (n + 1))} (h : maximally_consistent X) : ∀ α, X ⊢ ~α ↔ X ⊬ α := by
  intro α
  apply Iff.intro

  · intro hn
    apply by_contradiction
    intro hp; simp only [not_not] at hp
    have hXinc : inconsistent X := by
        simp [inconsistent, consistent, not_exists, not_not]
        exact Gentzen.not₁ hp hn
    exact hXinc h.left

  · intro hp
    simp only at hp
    have hX_cons_ext := derivable_pos_iff.not.mp hp
    have h' : ~α ∈ X := by
      apply by_contradiction
      · intro hn
        have hXnα_inc := h.right (~α) hn
        simp [inconsistent, consistent, not_exists] at hXnα_inc
        have hXnα_bot := hXnα_inc ⊥
        simp at hX_cons_ext
        contradiction

    apply Gentzen.mono Gentzen.init (Set.singleton_subset_iff.mpr h')

/-- Definition of satisfiability of a set of formulas `X`. -/
abbrev satisfiable (X : Set (𝓢.Formula n)) := ∃ (w : Model n), w ⊨ X

/--
  Lemma 4.5: The propositional equivalent to the model existence theorem. Any
  maximally consistent set `X` has a model.
-/
lemma maximally_consistent_satisfiable {X : Set (𝓢.Formula (n + 1))} (h₁ : maximally_consistent X) :
  satisfiable X := by
  let w : Model (n + 1) := ⟨fun i => @decide (X ⊢ (.var i)) (Classical.propDecidable _)⟩

  suffices iff : ∀ α, X ⊢ α ↔ w ⊨ α
  · apply Exists.intro w
    intro α hα
    exact (iff α).mp (mem_provable hα)

  intro α
  induction' α with i a s φs φs_ih
  · simp only [Satisfies.satisfies, Model.value, decide_eq_true_eq]
  · match a with
    | 1 => match s with
      | .not =>
        simp [Satisfies.satisfies, Model.value, Interpretation.fns]
        apply Iff.intro
        · intro h
          have imp := (φs_ih 0).not.mp
          simp only [Satisfies.satisfies, ne_eq, Bool.not_eq_true] at imp
          have hnφs₀ : X ⊬ (φs 0) := by
            have hφs : ![φs 0] = φs := List.ofFn_inj.mp rfl
            apply consistent₂ h₁.left ?h
            simp only [Tilde.tilde, hφs, h]
          exact imp hnφs₀
        · intro h
          have imp := (φs_ih 0).not.mpr
          simp only [Satisfies.satisfies, ne_eq, Bool.not_eq_true] at imp
          have hXnφs₀ := (maximally_consistent_neg h₁ _).mpr (imp h)
          have hφs : ![φs 0] = φs := List.ofFn_inj.mp rfl
          simp [Tilde.tilde, hφs] at hXnφs₀
          exact hXnφs₀

    | 2 => match s with
      | .and =>
        simp [Satisfies.satisfies, Model.value, Interpretation.fns]
        sorry

/-- Theorem 4.6: `X ⊢ α ↔ X ⊨ α` for all `X` and `α`. -/
theorem completeness {X : Set (𝓢.Formula (n + 1))} {α : 𝓢.Formula (n + 1)} :
  X ⊢ α ↔ X ⊨ α := by
  apply Iff.intro soundness
  · contrapose
    intro hnXα
    have hXαcon : consistent (X ∪ {~α}) := ⟨⊥, derivable_pos_iff.not.mp hnXα⟩
    have ⟨Y, hY⟩ := consistent_maximal_extension hXαcon
    have ⟨w, hw⟩ := maximally_consistent_satisfiable hY.right
    have hXsub : X ⊆ Y := (Set.union_subset_iff.mp hY.left).left
    have hwX : w ⊨ X := fun α hα => hw α (hXsub hα)

    intro hXα
    have hα : w ⊨ α := hXα w hwX
    have hwnα : w ⊨ ~α := hw (~α) (Set.singleton_subset_iff.mp (Set.union_subset_iff.mp hY.left).right)

    simp [Satisfies.satisfies, Model.value, Interpretation.fns] at hwnα hα
    rw [hα] at hwnα

    contradiction

/--
  Theorem 4.7: If `X ⊨ α`, then there is a finite subset `X₀ ⊆ X` such that `X₀ ⊨ α`.
  This is the analog to 4.1 but with `⊨` instead of `⊢`.
-/
theorem finiteness' {X : Set (𝓢.Formula (n + 1))} {α : 𝓢.Formula (n + 1)} (h : X ⊨ α) :
    ∃ X₀ ⊆ X, X₀.Finite ∧ (X₀ ⊨ α) := by
  have ⟨X₀, hsub, hfin, hsat⟩ := finiteness (completeness.mpr h)
  exact ⟨X₀, hsub, hfin, completeness.mp hsat⟩

/--
  Theorem 4.8: Propositional compactness theorem.
  A set `X` of propositional formulas is satisfiable if each finite subset of `X` is satisfiable.
-/
theorem compactness {X : Set (𝓢.Formula (n + 1))} {α : 𝓢.Formula (n + 1)}
    (h : ∀ X₀ ⊆ X, X₀.Finite → satisfiable X₀) : satisfiable X := by
  by_contra hsat
  have h' : X ⊨ (⊥ : 𝓢.Formula (n + 1)) := by
    intro w hw
    rw [not_exists] at hsat
    have := hsat w hw
    contradiction

  /- If `X ⊨ ⊥` then `X` has no model. -/
  have {X : Set (𝓢.Formula (n + 1))} (hX : X ⊨ (⊥ : 𝓢.Formula (n + 1))) (w : Model (n + 1)) :
      w ⊭ X := by
    intro hw
    simp [Satisfies.satisfies] at hX
    have hbot := hX w hw
    simp [Model.value, Interpretation.fns, Bool.and_not_self] at hbot

  have ⟨X₀, hsub, hfin, hX₀⟩ := finiteness' h'
  have hX₀sat := h X₀ hsub hfin
  have hX₀not_sat : ¬ satisfiable X₀ := by
    simp only [satisfiable, not_exists]
    exact this hX₀

  exact hX₀not_sat hX₀sat

end Section4
end Chapter1
