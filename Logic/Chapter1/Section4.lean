import Mathlib.Data.Set.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.Zorn
import «MathlibExt».Chain
import «MathlibExt».Set
import «Logic».Chapter1.Section3

open Notation

section Gentzen

set_option hygiene false
scoped[Notation] infix:40 " ⊢ " => Gentzen
scoped[Notation] infix:40 " ⊬ " => fun X α => ¬ Gentzen X α

/--
  Gentzen Sequents is a relation from sets of formulas to formulas with specific construction rules.

  The choice of signature `Bₐ = {¬, ∧}` is for convenience as it has few symbols and is functional
  complete.
-/
inductive Gentzen : Set (Bₐ.Formula V) → (Bₐ.Formula V) → Prop
  /-- (IS) Initial sequent. -/
  | init : {α} ⊢ α
  /-- (MR) Monotonicity -/
  | mono (hα : X ⊢ α) (hX : X ⊆ X') : X' ⊢ α
  /-- (∧1) And introduction. -/
  | and₁ (hα : X ⊢ α) (hβ : X ⊢ β) : X ⊢ (α ⋏ β)
  /-- (∧2 left) And elimination into left. -/
  | and₂_left  (hX : X ⊢ α ⋏ β) : X ⊢ α
  /-- (∧2 left) And elimination into right. -/
  | and₂_right (hX : X ⊢ α ⋏ β) : X ⊢ β
  /-- (¬1) Absurd. -/
  | not₁ (h₁ : X ⊢ α) (h₂ : X ⊢ ~α) β : X ⊢ β
  /-- (¬2) By cases. -/
  | not₂ (h₁ : X ∪ {α} ⊢ β) (h₂ : X ∪ {~α} ⊢ β) : X ⊢ β

namespace Gentzen

variable [Inhabited V] {X : Set (Bₐ.Formula V)} {α : Bₐ.Formula V}

theorem and₂_iff : X ⊢ α ⋏ β ↔ X ⊢ α ∧ X ⊢ β :=
  ⟨fun h => ⟨.and₂_left h, .and₂_right h⟩, fun ⟨h₁, h₂⟩ => .and₁ h₁ h₂⟩

theorem mem (h : α ∈ X) : X ⊢ α := mono init (Set.singleton_subset_iff.mpr h)

theorem union_singleton_right : X ∪ {α} ⊢ α := mono init (Set.subset_union_right X {α})

theorem union_singleton_left : {α} ∪ X ⊢ α := mono init (Set.subset_union_left {α} X)

theorem not_elim (h : X ∪ {~α} ⊢ α) : X ⊢ α := not₂ union_singleton_right h

theorem absurd (h₁ : X ∪ {~α} ⊢ β) (h₂ : X ∪ {~α} ⊢ ~β) : X ⊢ α := not_elim (not₁ h₁ h₂ α)

theorem cut (h₁ : X ⊢ α) (h₂ : X ∪ {α} ⊢ β) : X ⊢ β :=
  not₂ h₂ (not₁ (mono h₁ (Set.subset_union_left _ {~α})) union_singleton_right β)

theorem arrow_elim (h : X ⊢ α ⟶ β) : X ∪ {α} ⊢ β := by
  apply not_elim
  · apply not₁
    · apply and₁
      rw [Set.union_comm, ← Set.union_assoc]
      exact union_singleton_right
      exact union_singleton_right
    · rw [Set.union_assoc]
      exact mono h (Set.subset_union_left _ _)

theorem arrow_intro (h : X ∪ {α} ⊢ β) : X ⊢ α ⟶ β := by
  have h1 : X ∪ {α ⋏ ~β} ∪ {α} ⊢ β := by
    rw [Set.union_assoc, Set.union_comm _ {α}, ← Set.union_assoc]
    exact mono h (Set.subset_union_left _ _)
  have h2 : X ∪ {α ⋏ ~β} ⊢ α := and₂_left union_singleton_right
  have h3 : X ∪ {α ⋏ ~β} ⊢ β := cut h2 h1
  have h4 : X ∪ {α ⋏ ~β} ⊢ ~β := and₂_right union_singleton_right
  have h5 : X ∪ {α ⋏ ~β} ⊢ α ⟶ β := not₁ h3 h4 _
  have h6 : X ∪ {~(α ⋏ ~β)} ⊢ α ⟶ β := union_singleton_right
  exact not₂ h5 h6

theorem detachment (h₁ : X ⊢ α) (h₂ : X ⊢ α ⟶ β) : X ⊢ β := cut h₁ (arrow_elim h₂)

theorem false_elim (h : X ⊢ ⊥) α : X ⊢ α := .not₁ (.and₂_left h) (.and₂_right h) α

structure ClosedRel (P : (Set (Bₐ.Formula V)) → Bₐ.Formula V → Prop) where
  init {α} : P {α} α
  mono {X α} : P X α → X ⊆ X' → P X' α
  and₁ {X α} : P X α → P X β → P X (α ⋏ β)
  and₂_left {X α β} : P X (α ⋏ β) → P X α
  and₂_right {X α β} : P X (α ⋏ β) → P X β
  not₁ {X α} β : P X α → P X (~α) → P X β
  not₂ {X α β} : P (X ∪ {α}) β → P (X ∪ {~α}) β → P X β

/--
  Principle of rule induction for Gentzen Sequents.
-/
theorem induction (r : ClosedRel P) (h : X ⊢ α) : P X α := by
  induction h
  case init => exact r.init
  case mono hX hα => exact r.mono hα hX
  case and₁ hα hβ => exact r.and₁ hα hβ
  case and₂_left hX => exact r.and₂_left hX
  case and₂_right hX => exact r.and₂_right hX
  case not₁ β hXα hXnα => exact r.not₁ β hXα hXnα
  case not₂ hXα hXnα => exact r.not₂ hXα hXnα

/-- The soundness of `⊢`. Alternatively, `⊢ ⊆ ⊨`. -/
theorem soundness (h : X ⊢ α) : X ⊨ α := by
  refine' induction _ h
  constructor
  case init =>
    simp only [Satisfies.satisfies, Set.mem_singleton_iff, forall_eq, imp_self,
      implies_true, forall_const]
  case mono =>
    intro X α X' hXα hXX' w hwX'
    exact hXα w (fun x hx => hwX' x (hXX' hx))
  case and₁ =>
    intro X α β hα hβ w hw
    simp only [Model.satisfies_and, hα w hw, hβ w hw, and_self]
  case and₂_left => exact fun hXαβ w hw => (w.satisfies_and.mp (hXαβ w hw)).left
  case and₂_right => exact fun hXαβ w hw => (w.satisfies_and.mp (hXαβ w hw)).right
  case not₁ =>
    intro X α β hXα hXnα w hw
    simp only [Satisfies.satisfies, Model.value_not, Bool.not_eq_true'] at hXα hXnα
    have := hXα w hw ▸ hXnα w hw
    contradiction
  case not₂ =>
    intro X α β hXα hXnα w hw
    simp only [Satisfies.satisfies] at hXα hXnα
    by_cases hα : w.value α = true
    · suffices : ∀ α' ∈ X ∪ {α}, w.value α' = true
      · exact hXα w this
      intro α' hα'
      refine' Or.elim hα' (fun hα'X => hw α' hα'X) (fun hα'α => _)
      · simp only [Set.mem_singleton_iff.mp hα'α, hα]
    · suffices : ∀ α' ∈ X ∪ {~α}, w.value α' = true
      · exact hXnα w this
      intro α' hα'
      refine' Or.elim hα' (fun hα'X => hw α' hα'X) (fun hα'α => _)
      · simp only [Set.mem_singleton_iff.mp hα'α, Model.value_not, hα, Bool.not_false]

/--
  Theorem 4.1: Finiteness theorem for `⊢`.

  This is proved by showing that the property `P(X, α) = ∃ X₀ ⊆ X, X₀.Finite ∧ X₀ ⊢ α` is closed
  under Gentzen rules.
-/
theorem finiteness (h : X ⊢ α) : ∃ X₀ ⊆ X, X₀.Finite ∧ X₀ ⊢ α := by

  suffices : ClosedRel (fun X (α : Bₐ.Formula V) => ∃ X₀ ⊆ X, X₀.Finite ∧ X₀ ⊢ α)
  · exact induction this h

  constructor
  case init => exact fun {α} => ⟨{α}, subset_refl _, Set.finite_singleton α, init⟩
  case mono => exact fun ⟨X₀, hs, hf, hα⟩ hs' => ⟨X₀, subset_trans hs hs', hf, hα⟩
  case and₁ =>
    intro X α β ⟨X₀α, hαs, hαf, hα⟩ ⟨X₀β, hβs, hβf, hβ⟩
    refine' ⟨X₀α ∪ X₀β, Set.union_subset hαs hβs, Set.Finite.union hαf hβf, _⟩
    exact and₁ (mono hα (Set.subset_union_left _ _)) (mono hβ (Set.subset_union_right _ _))
  case and₂_left => exact fun ⟨X₀, hs, hf, hα⟩ => ⟨X₀, hs, hf, and₂_left hα⟩
  case and₂_right => exact fun ⟨X₀, hs, hf, hα⟩ => ⟨X₀, hs, hf, and₂_right hα⟩
  case not₁ =>
    intro X α β ⟨X₀α, h₀s, h₀f, h₀α⟩ ⟨X₁α, h₁s, h₁f, h₁α⟩
    refine' ⟨X₀α ∪ X₁α, Set.union_subset h₀s h₁s, Set.Finite.union h₀f h₁f, _⟩
    exact not₁ (mono h₀α (Set.subset_union_left _ _)) (mono h₁α (Set.subset_union_right _ _)) β
  case not₂ =>
    intro X α β ⟨X₀α, h₀s, h₀f, h₀α⟩ ⟨X₁α, h₁s, h₁f, h₁α⟩
    refine' ⟨(X₀α \ {α}) ∪ (X₁α \ {~α}), ?hs, ?hf, ?hα⟩
    case hs =>
      refine' Set.union_subset _ _
      · intro x hx
        have ⟨hx₀, hxα⟩ := (Set.mem_diff _).mp hx
        refine' Or.elim (h₀s hx₀) id fun hxα' => (hxα hxα').elim
      · intro x hx
        have ⟨hx₁, hxα⟩ := (Set.mem_diff _).mp hx
        refine' Or.elim (h₁s hx₁) id fun hxα' => (hxα hxα').elim
    case hf =>
      exact Set.Finite.union (Set.Finite.diff h₀f {α}) (Set.Finite.diff h₁f {~α})
    case hα =>
      apply not₂ (α := α)
      · rw [Set.union_comm (X₀α \ {α}), Set.union_assoc, Set.diff_union_self]
        exact mono h₀α (Set.subset_union_of_subset_right (Set.subset_union_left _ _) _)
      · rw [Set.union_assoc, Set.diff_union_self]
        exact mono h₁α (Set.subset_union_of_subset_right (Set.subset_union_left _ _) _)

end Gentzen
end Gentzen

section Consistency

/-- A set of formulas is inconsistent if all formulas are provable from it. -/
def inconsistent (X : Set (Bₐ.Formula V)) := ∀ α, X ⊢ α

def consistent (X : Set (Bₐ.Formula V)) := ¬ inconsistent X

def maximally_consistent (X : Set (Bₐ.Formula V)) := consistent X ∧ ∀ X' ⊃ X, inconsistent X'

variable [Inhabited V] {X : Set (Bₐ.Formula V)} {α : Bₐ.Formula V}

/-- Inconsistency is equivalent to the derivability of `⊥`. -/
theorem inconsistent_iff : inconsistent X ↔ X ⊢ ⊥ :=
  ⟨fun h => h ⊥, fun h => .not₁ (.and₂_left h) (.and₂_right h)⟩

/--
  Maximal consistency is equivalent to `∀ α (exactly one of) α ∈ X ∨ ~α ∈ X`.

  Note: only the reverse direction requires `Inhabited V`.
-/
theorem maximally_consistent_iff (h : consistent X) :
    maximally_consistent X ↔ ∀ α, (α ∈ X ∧ ~α ∉ X) ∨ (α ∉ X ∧ ~α ∈ X) := by
  refine' ⟨fun h α => _, fun hmc => ⟨h, _⟩⟩
  · by_contra hα
    simp only [not_or, not_and_or, not_not] at hα
    have ⟨h₁, h₂⟩ := hα
    refine' Or.elim h₁ (fun hα => _) (fun hnα => _)
    · have hnα : ~α ∉ X := Or.elim h₂ (absurd · hα) id
      have h₁s : X ∪ {α} ⊃ X :=
        (Set.ssubset_iff_of_subset (Set.subset_union_left _ _)).mpr
          ⟨α, Set.mem_union_right _ (Set.mem_singleton α), hα⟩
      have h₂s : X ∪ {~α} ⊃ X :=
        (Set.ssubset_iff_of_subset (Set.subset_union_left _ _)).mpr
          ⟨~α, Set.mem_union_right _ (Set.mem_singleton (~α)), hnα⟩
      exact h.left fun β => .not₂ (h.right _ h₁s β) (h.right _ h₂s β)
    · have hα : X ⊢ α := .mem (Or.elim h₂ id (absurd hnα ·))
      have hnα : X ⊢ ~α := .mem hnα
      exact h.left (.not₁ hα hnα)
  · intro X' hX'
    have ⟨φ, hφ', hφ⟩ := Set.ssubset_exists_mem_not_mem hX'
    have hnφ : ~φ ∈ X' := by
      apply Set.mem_of_subset_of_mem hX'.left
      exact Or.elim (hmc φ) (fun ⟨hφ', _⟩ => absurd hφ' hφ) (fun ⟨_, hnφ⟩ => hnφ)
    exact .not₁ (.mem hφ') (.mem hnφ)

/-- Lemma 4.2: C⁺ -/
theorem derivable_iff : X ⊢ α ↔ X ∪ {~α} ⊢ ⊥ := ⟨
  fun h => .not₁ (.mono h (Set.subset_union_left _ _)) .union_singleton_right ⊥,
  fun h => .not₂ .union_singleton_right (.false_elim h α)⟩

/-- Lemma 4.2: C⁻ -/
theorem derivable_not_iff : X ⊢ ~α ↔ X ∪ {α} ⊢ ⊥ := ⟨
  fun h => .not₁ .union_singleton_right (.mono h (Set.subset_union_left _ _)) ⊥,
  fun h => .not₂ (.false_elim h (~α)) .union_singleton_right⟩

/-- Lemma 4.3: Lindenbaum's theorem. -/
theorem consistent_maximal_extension (h : consistent X) : ∃ X' ⊇ X, maximally_consistent X' := by
  let H := {X' | X ⊆ X' ∧ consistent X'}
  have ⟨X₀, ⟨hXsubX₀, hX₀con⟩, hX₀max⟩ : ∃ X₀ ∈ H, ∀ Y ∈ H, X₀ ⊆ Y → Y = X₀ := by
    refine' zorn_subset H (fun K hKsub hKchain => _)
    wlog hKnonempty : ∃ Y, Y ∈ K
    · exact ⟨X, ⟨Eq.subset rfl, h⟩, fun Y hY => (not_exists.mp hKnonempty Y hY).elim⟩
    let U := ⋃₀ K
    suffices hU : U ∈ H
    · exact ⟨U, hU, fun Y hY => Set.subset_sUnion_of_mem hY⟩
    have hXsubU : X ⊆ U := by
      intro α hα
      simp only [Set.mem_sUnion]
      have ⟨Y, hY⟩ := hKnonempty
      exact ⟨Y, hY, (hKsub hY).left hα⟩
    have hUcon : consistent U := by
      by_contra hU
      simp only [consistent, not_exists, not_not] at hU
      have ⟨U₀, hU₀subU, hU₀fin, hU₀bot⟩ := Gentzen.finiteness (hU ⊥)
      have map : ∀ αᵢ ∈ U₀, ∃ Yᵢ ∈ K, αᵢ ∈ Yᵢ := fun αᵢ hαᵢ => hU₀subU hαᵢ
      have ⟨Y, hYmem, hYsub⟩ : ∃ Y ∈ K, U₀ ⊆ Y := Chain.fin_subset_max hKnonempty hKchain hU₀fin map
      have hYcon : consistent Y := (hKsub hYmem).right
      have hYinc : inconsistent Y := inconsistent_iff.mpr (Gentzen.mono hU₀bot hYsub)
      contradiction
    exact ⟨hXsubU, hUcon⟩
  have hX₀ : maximally_consistent X₀ := by
    refine' ⟨hX₀con, _⟩
    by_contra hX₁
    simp only [not_forall] at hX₁
    have ⟨X₁, ⟨hX₁sup, hX₁ne⟩, hX₁con⟩ := hX₁
    simp only [hX₀max X₁ ⟨hXsubX₀.trans hX₁sup, hX₁con⟩ hX₁sup, subset_rfl, not_true] at hX₁ne
  exact ⟨X₀, hXsubX₀, hX₀⟩

theorem maximally_consistent_union_singleton (hXmcon : maximally_consistent X)
    (hXαcon : consistent (X ∪ {α})) : α ∈ X := by
  by_contra hα
  have hXssubXα : X ⊂ X ∪ {α} := by
    exact ⟨
      Set.subset_union_left _ _,
      Set.not_subset_iff_exists_mem_not_mem.mpr ⟨α, Set.mem_union_right _ (Set.mem_singleton α), hα⟩
    ⟩
  exact hXαcon (hXmcon.right _ hXssubXα)

/-- Lemma 4.4: A maximally consistent set `X` has the property `X ⊢ ¬α ↔ X ⊬ α`, for any `α`. -/
theorem maximally_consistent_derives_not_iff (hX : maximally_consistent X) : X ⊢ ~α ↔ X ⊬ α := by
  refine' ⟨fun hXnα => by_contra fun hXα => _, fun hXα => _⟩
  · simp only [not_not] at hXα
    exact hX.left (Gentzen.not₁ hXα hXnα)
  · simp only at hXα
    have hXnαcon := inconsistent_iff.not.mpr (derivable_iff.not.mp hXα)
    exact Gentzen.mem (maximally_consistent_union_singleton hX hXnαcon)

/-- Lemma 4.5: A maximally consistent set `X` is satisfiable. -/
theorem maximally_consistent_satisfiable (hX : maximally_consistent X) : ∃ w : Model V, w ⊨ X := by
  have Gentzen.decidable (X : Set (Bₐ.Formula V)) v : Decidable (X ⊢ v) := Classical.dec (X ⊢ v)
  let w : Model V := ⟨fun v => decide (X ⊢ .var v)⟩
  have derives_imp_satisfies {α} : X ⊢ α ↔ w ⊨ α := by
    induction α using Bₐ.induction
    case var v =>
      simp only [Model.satisfies_formula, Model.value, decide_eq_true_eq]
    case not α hα_ih =>
      simp only [maximally_consistent_derives_not_iff hX, hα_ih.not,
        Model.satisfies_formula, Model.value_not, Bool.not_eq_true, Bool.not_eq_true']
    case and α β hα_ih hβ_ih =>
      rw [Gentzen.and₂_iff, hα_ih, hβ_ih, Model.satisfies_and]
  exact ⟨w, fun α hα => derives_imp_satisfies.mp (Gentzen.mem hα)⟩

/-- Theorem 4.6: Completeness theorem for propositional logic. -/
theorem Gentzen.completeness : X ⊢ α ↔ X ⊨ α := by
  refine' ⟨Gentzen.soundness, not_imp_not.mp fun hXα => _⟩
  have hXnα_con : consistent (X ∪ {~α}) := not_forall.mpr ⟨⊥, derivable_iff.not.mp hXα⟩
  have ⟨Y, hYsup, hYmcon⟩ := consistent_maximal_extension hXnα_con
  have ⟨w, hw⟩ := maximally_consistent_satisfiable hYmcon
  have hXnαw : w ⊨ X ∪ {~α} := fun β hβ => hw β (hYsup hβ)
  have ⟨hwX, hwα⟩ := w.satisfies_union.mp hXnαw
  simp only [Satisfies.satisfies, Bool.not_eq_true, not_forall, exists_prop]
  exact ⟨w, hwX, w.satisfies_not'.mp hwα⟩

/-- Theorem 4.7: Finiteness theorem for `⊨`. -/
theorem Satisfies.finiteness (h : X ⊨ α) : ∃ X₀ ⊆ X, X₀.Finite ∧ X₀ ⊨ α :=
  have ⟨X₀, hX₀s, hX₀f, hX₀⟩ := Gentzen.finiteness (Gentzen.completeness.mpr h)
  ⟨X₀, hX₀s, hX₀f, Gentzen.completeness.mp hX₀⟩

/-- Theorem 4.8: Propositional compactness theorem. -/
theorem Satisfies.compactness (h : ∀ X₀ ⊆ X, X₀.Finite → satisfiable_set X₀) :
    satisfiable_set X := by
  by_contra hX
  have hXbot : X ⊨ (⊥ : Bₐ.Formula V) := fun w hw => absurd hw (not_exists.mp hX w)
  have ⟨X₀, hX₀s, hX₀f, hX₀bot⟩ := finiteness hXbot
  have ⟨w, hw⟩ := h X₀ hX₀s hX₀f
  have hwbot := hX₀bot w hw
  simp only [satisfies, Model.value_bot] at hwbot

end Consistency
