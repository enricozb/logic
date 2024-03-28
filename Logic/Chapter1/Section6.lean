import Mathlib.Data.Set.Finite
import «MathlibExt».Fin
import «Logic».Chapter1.Section3
import «Logic».Chapter1.Section4

open Notation

section Proof

def Λ₁ : Set (Bₐ.Formula V) :=
  {(α ⟶ β ⟶ γ) ⟶ (α ⟶ β) ⟶ α ⟶ γ | (α : Bₐ.Formula V) (β : Bₐ.Formula V) (γ : Bₐ.Formula V)}

def Λ₂ : Set (Bₐ.Formula V) :=
  {α ⟶ β ⟶ α ⋏ β | (α : Bₐ.Formula V) (β : Bₐ.Formula V)}

def Λ₃ : Set (Bₐ.Formula V) :=
  {α ⋏ β ⟶ α | (α : Bₐ.Formula V) (β : Bₐ.Formula V)} ∪
  {α ⋏ β ⟶ β | (α : Bₐ.Formula V) (β : Bₐ.Formula V)}

def Λ₄ : Set (Bₐ.Formula V) :=
  {(α ⟶ ~β) ⟶ β ⟶ ~α | (α : Bₐ.Formula V) (β : Bₐ.Formula V)}

def Λ : Set (Bₐ.Formula V) := Λ₁ ∪ Λ₂ ∪ Λ₃ ∪ Λ₄

/--
  A proof of `α` from `X` of size `n + 1` is a sequence of formulas `φs = [φ₀, .., φₙ]` of
  length `n` such that `φₙ = α` and for every `φₖ` in `φs` either
  - `φₖ ∈ X ∪ Λ` (assumption or tautology)
  - `∃ i < k, j < k, φⱼ = φᵢ → φₖ` (modus ponens)
-/
structure Proof (X : Set (Bₐ.Formula V)) (α : Bₐ.Formula V) (n : ℕ) where
  φs : [Bₐ.Formula V; (n + 1)]
  valid : ∀ k, φs k ∈ X ∪ Λ ∨ ∃ i < k, ∃ j < k, φs j = φs i ⟶ φs k
  conclusion : φs (Fin.last n) = α

namespace Proof

example {p q : Bₐ.Formula V} : Proof {p, q} (p ⋏ q) 4 := by
  refine' ⟨![p, q, p ⟶ q ⟶ p ⋏ q, q ⟶ p ⋏ q, p ⋏ q], fun k => _, rfl⟩
  match k with
  | 0 => exact Or.inl (Set.mem_union_left _ (Set.mem_insert _ _))
  | 1 => exact Or.inl (Set.mem_union_left _  (Set.mem_insert_iff.mpr
    (Or.inr (Set.mem_singleton_iff.mpr rfl))))
  | 2 => exact Or.inl (Set.mem_union_right _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_right _ ⟨p, q, rfl⟩))))
  | 3 => exact Or.inr ⟨0, Nat.le.step (Nat.le.step Nat.le.refl), 2, Nat.le.refl, rfl⟩
  | 4 => exact Or.inr ⟨1, Nat.le.step (Nat.le.step Nat.le.refl), 3, Nat.le.refl, rfl⟩

def size (_ : Proof X α n) : ℕ := n + 1

/-- Any prefix of a proof `φs` is also a proof. -/
def init (p : Proof X α n) (h : k < n) : Proof X (p.φs k) k := by
  refine' ⟨Fin.init' p.φs (add_lt_add_right h 1), fun k' => _, _⟩
  · refine' Or.elim (p.valid k') (fun hk' => Or.inl _) (fun ⟨i, hi, j, hj, hk'⟩ => Or.inr _)
    · rw [Fin.init'_lt]
      sorry
    · sorry
  · simp only [Fin.init', Fin.val_last]
    rw [← (Fin.eq_mk_iff_val_eq (hk := h.trans (lt_add_one n))).mpr]
    exact Fin.val_cast_of_lt (Nat.le.step h)

-- def Proof.init (p : Proof X α n) (h : k < n) : Proof X (p.φs k) k := by
--   refine' ⟨Fin.init' p.φs (add_lt_add_right h 1), _, _⟩
--   · intro k'
--     refine' Or.elim (p.valid k') (fun hk' => Or.inl _) (fun ⟨i, hi, j, hj, hk'⟩ => Or.inr _)
--     · have : (↑↑k' : Fin (n + 1)) = ⟨↑k', k'.prop.trans (add_lt_add_right h 1)⟩ := by
--         simp only [Fin.eq_mk_iff_val_eq, Fin.val_nat_cast, Nat.mod_succ_eq_iff_lt]
--         exact k'.prop.trans (add_lt_add_right h 1)
--       simp only [Fin.init', ← this, hk']
--     · have hk'coe : ↑(↑(↑k' : ℕ) : Fin (n + 1)) = (↑k' : ℕ) := by
--         simp only [Fin.val_nat_cast, Nat.mod_succ_eq_iff_lt]
--         exact k'.prop.trans (add_lt_add_right h 1)
--       refine' ⟨i, _, j, _, _⟩
--       · have hik : ↑i < k + 1 := sorry
--         apply Fin.mk_lt_mk.mpr
--         rw [Nat.mod_eq_of_lt hik, ← hk'coe]
--         exact Fin.lt_iff_val_lt_val.mp hi
--       · have hjk : ↑j < k + 1 := sorry
--         apply Fin.mk_lt_mk.mpr
--         rw [Nat.mod_eq_of_lt hjk, ← hk'coe]
--         exact Fin.lt_iff_val_lt_val.mp hj
--       · have hicoe : ↑(↑(↑i : ℕ) : Fin (k + 1)) = (↑i : ℕ) := sorry
--         have hjcoe : ↑(↑(↑j : ℕ) : Fin (k + 1)) = (↑j : ℕ) := sorry
--         simp only [Fin.init'_lt]
--         simp_rw [hicoe, hjcoe]
--   · simp only [Fin.init', Fin.val_last]
--     rw [← (Fin.eq_mk_iff_val_eq (hk := h.trans (lt_add_one n))).mpr]
--     exact Fin.val_cast_of_lt (Nat.le.step h)

end Proof
end Proof

/-- A relation between sets of formulas and formulas. -/
class Hilbert (α : Sort _) (β : Sort _) where
  proves : α → β → Prop

scoped[Notation] infix:40 " |~ " => Hilbert.proves

instance : Hilbert (Set (Bₐ.Formula V)) (Bₐ.Formula V) where
  proves X α := ∃ n, Nonempty (Proof X α n)

instance : Hilbert (Set (Bₐ.Formula V)) (Set (Bₐ.Formula V)) where
  proves X Y := ∀ α ∈ Y, X |~ α

namespace Hilbert

section Lemmas

variables {X X' : Set (Bₐ.Formula V)} {α β : Bₐ.Formula V}

lemma singleton (α : Bₐ.Formula V) : ({α} : Set _) |~ α := by
  refine' ⟨0, ⟨![α], fun k => Or.inl _, _⟩⟩
  all_goals simp only [Matrix.cons_val_fin_one, Set.mem_union, Set.mem_singleton α, true_or]

lemma mono (hX : X ⊆ X') (h : X |~ α) : X' |~ α := by
  have ⟨n, ⟨p⟩⟩ := h
  refine' ⟨n, ⟨p.φs, fun k => Or.elim (p.valid k)
    (fun hk => Or.inl (Or.elim hk (fun hk => Or.inl (hX hk)) (fun hk => Or.inr hk)))
    (fun hk => Or.inr hk),
    p.conclusion⟩⟩

lemma mp (hα : X |~ α) (hαβ : X |~ α ⟶ β) : X |~ β := by sorry
  -- need to concat the proofs of α, α ⟶ β, and append β

/-- Lemma 6.2.a. -/
lemma contrapositive (h : X |~ α ⟶ ~β) : X |~ β ⟶ ~α := by sorry

/-- Lemma 6.2.b. -/
lemma assumption : (∅ : Set (Bₐ.Formula V)) |~ α ⟶ β ⟶ α := by sorry

/-- Lemma 6.2.c. -/
lemma identity : (∅ : Set (Bₐ.Formula V)) |~ α ⟶ α := by sorry

/-- Lemma 6.2.d. -/
lemma imp_not_not : (∅ : Set (Bₐ.Formula V)) |~ α ⟶ ~~α := by sorry

/-- Lemma 6.2.e. -/
lemma imp_not_imp_absurd : (∅ : Set (Bₐ.Formula V)) |~ β ⟶ ~β ⟶ α := by sorry

/-- Lemma 6.3 (Deduction theorem). -/
lemma deduction (h : X ∪ {a} |~ β) : X |~ α ⟶ β := by sorry

/-- Lemma 6.4. -/
lemma not_not_imp : (∅ : Set (Bₐ.Formula V)) |~ ~~α ⟶ α := by sorry

/-- Lemma 6.5. -/
lemma not₂ (h₁ : X ∪ {β} |~ α) (h₂ : X ∪ {~β} |~ α) : X |~ α := by sorry

end Lemmas

/-- Theorem 6.1: Induction principle for Hilbert Calculi `|~`. -/
theorem induction (P : Bₐ.Formula V → Prop) (ho : ∀ α ∈ X ∪ Λ, P α)
    (hs : ∀ α β, P α → P (α ⟶ β) → P β) (hp : Proof X φ n) : P φ := by
  by_cases hφ : φ ∈ X ∪ Λ
  · exact ho φ hφ
  · refine' Or.elim (hp.valid (Fin.last n)) (fun h => absurd (hp.conclusion ▸ h) hφ) _
    match n with
    | 0 => exact (fun ⟨i, hi, _⟩ => absurd hi (Fin.not_lt_zero i))
    | n'+1 =>
      intro ⟨i, hi, j, hj, hij⟩
      have hpi := hp.init hi
      have hpj := hp.init hj
      have : hpi.size < hp.size := by simpa only [Proof.size, add_lt_add_iff_right]
      have : hpj.size < hp.size := by simpa only [Proof.size, add_lt_add_iff_right]
      rw [Fin.cast_val_eq_self] at hpi hpj
      have hφsi : P (hp.φs i) := Hilbert.induction P ho hs (Fin.cast_val_eq_self i ▸ hpi)
      have hφsj : P (hp.φs j) := Hilbert.induction P ho hs (Fin.cast_val_eq_self j ▸ hpj)
      rw [hij, hp.conclusion] at hφsj
      exact hs _ _ hφsi hφsj
termination_by _ => hp.size

variable {X : Set (Bₐ.Formula V)} {α β : Bₐ.Formula V}

/--
  Finiteness of `|~`.

  This can also be shown by identifying exactly which elements of `X` are used in the proof of `α`,
  which will be finite since proofs are finite.
-/
theorem finiteness (h : X |~ α) : ∃ X₀ ⊆ X, X₀.Finite ∧ X₀ |~ α := by
  have ⟨n, ⟨p⟩⟩ := h
  refine' Hilbert.induction
    (fun α => ∃ X₀ ⊆ X, X₀.Finite ∧ X₀ |~ α)
    (fun α hα => Or.elim hα (fun hαX => ⟨{α}, _⟩) (fun hαΛ => _))
    (fun α β ⟨Xα, hXαs, hXαf, hα⟩ ⟨Xβ, hXβs, hXβf, hβ⟩ => _)
    p
  · simp only [Set.singleton_subset_iff, Set.finite_singleton, hαX, true_and, singleton α]
  · refine' ⟨{}, X.empty_subset, Set.finite_empty, ⟨0, ![α], fun k => Or.inl _, _⟩⟩
    all_goals simp only [Matrix.cons_val_fin_one, Set.empty_union, hαΛ]
  · refine' ⟨Xα ∪ Xβ, Set.union_subset_iff.mpr ⟨hXαs, hXβs⟩, Set.finite_union.mpr ⟨hXαf, hXβf⟩, _⟩
    exact mp (mono (Xα.subset_union_left Xβ) hα) (mono (Xα.subset_union_right Xβ) hβ)

/-- Soundness of `|~`. Equivalently, `|~ ⊆ ⊨`. -/
theorem soundness (h : X |~ α) : X ⊨ α := by
  have ⟨n, ⟨p⟩⟩ := h
  refine' Hilbert.induction (X ⊨ ·)
    (fun α hα => Or.elim hα
      (fun hαX _ hw => hw α hαX)
      (fun hαΛ w _ => _))
    (fun _ _ hα hαβ w hw => w.satisfies_arrow.mp (hαβ w hw) (hα w hw))
    p
  · simp only [Set.mem_union, Λ, or_assoc] at hαΛ
    obtain ⟨α, β, γ, h₁⟩ | ⟨α, β, h₂⟩ | h₃ | ⟨α, β, h₄⟩ := hαΛ
    · simp_rw [← h₁, Model.satisfies_arrow]
      exact fun hαβγ hαβ hα => hαβγ hα (hαβ hα)
    · simp_rw [← h₂, Model.satisfies_arrow]
      exact fun hα hβ => w.satisfies_and.mpr ⟨hα, hβ⟩
    · refine' Or.elim h₃ (fun ⟨α, β, h₃⟩ => _) (fun ⟨α, β, h₃⟩ => _)
      · rw [← h₃]
        simp only [Model.satisfies_arrow, Model.satisfies_and]
        exact fun ⟨hα, _⟩ => hα
      · rw [← h₃]
        simp only [Model.satisfies_arrow, Model.satisfies_and]
        exact fun ⟨_, hβ⟩ => hβ
    · simp_rw [← h₄, Model.satisfies_arrow, Model.satisfies_not]
      exact fun hαnβ hβ hα => hαnβ hα hβ

/-- Theorem 6.6 (Completeness theorem). `|~ = ⊨`. -/
theorem completeness [Inhabited V] : X |~ α ↔ X ⊨ α := by
  refine' Iff.intro soundness (fun hXα => _)
  refine' Gentzen.induction _ (Gentzen.completeness.mpr hXα)
  constructor
  · exact fun {α} => singleton α
  · exact fun {X X' α} hX'α hXs => mono hXs hX'α
  · sorry -- X |~ α → X |~ β → X |~ α ⋏ β
  · sorry -- X |~ α ⋏ β → X |~ α
  · sorry -- X |~ α ⋏ β → X |~ β
  · sorry -- X |~ α → X |~ ~α → X |~ β
  · exact fun {X α β} h₁ h₂ => not₂ h₁ h₂

end Hilbert
