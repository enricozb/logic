import Mathlib.Data.Set.Finite
import «MathlibExt».Fin
import «Logic».Chapter1.Section3

open Notation

section Hilbert

def Λ₁ : Set (Bₐ.Formula V) :=
  {(α ⟶ β ⟶ γ) ⟶ (α ⟶ β) ⟶ α ⟶ γ | (α : Bₐ.Formula V) (β : Bₐ.Formula V) (γ : Bₐ.Formula V)}

def Λ₂ : Set (Bₐ.Formula V) :=
  {α ⟶ β ⟶ α ⋏ β | (α : Bₐ.Formula V) (β : Bₐ.Formula V)}

def Λ₃ : Set (Bₐ.Formula V) :=
  {α ⋏ β ⟶ α | (α : Bₐ.Formula V) (β : Bₐ.Formula V)} ∪
  {α ⋏ β ⟶ β | (α : Bₐ.Formula V) (β : Bₐ.Formula V)}

def Λ₄ : Set (Bₐ.Formula V) :=
  {(α ⟶ ~β) ⟶ β ⟶ ~α | (α : Bₐ.Formula V) (β : Bₐ.Formula V)}

abbrev Λ : Set (Bₐ.Formula V) := Λ₁ ∪ Λ₂ ∪ Λ₃ ∪ Λ₄

lemma mem_Λ {P : Bₐ.Formula V → Prop}
    (h₁ : α ∈ Λ₁ → P α) (h₂ : α ∈ Λ₂ → P α) (h₃ : α ∈ Λ₃ → P α) (h₄ : α ∈ Λ₄ → P α)
    (h : α ∈ Λ) : P α :=
  Or.elim h (Or.elim · (Or.elim · h₁ h₂) h₃) h₄

def is_proof (φs : [Bₐ.Formula V; n + 1]) (X : Set (Bₐ.Formula V)) :=
    ∀ k, φs k ∈ X ∪ Λ ∨ ∃ i < k, ∃ j < k, φs j = φs i ⟶ φs k

/--
  A proof of `α` from `X` of size `n + 1` is a sequence of formulas `φs` of length `n` such that
  `φₙ = α` and for every `φₖ` in `φs` either
  - `φₖ ∈ X ∪ Λ` (assumption)
  - `∃ i < k, j < k, φⱼ = φᵢ → φₖ` (modus ponens)
-/
structure Proof (X : Set (Bₐ.Formula V)) (α : Bₐ.Formula V) (n : ℕ) where
  φs : [Bₐ.Formula V; (n + 1)]
  valid : is_proof φs X
  conclusion : φs (Fin.last n) = α

def Proof.size (_ : Proof X α n) : ℕ := n + 1

/-- Any prefix of a proof `φs` is also a proof. -/
def Proof.init (p : Proof X α n) (h : k < n) : Proof X (p.φs k) k := sorry
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

/-- A relation between sets of formulas and formulas. -/
class Proves (α : Sort _) (β : Sort _) where
  proves : α → β → Prop

scoped[Notation] infix:40 " |~ " => Proves.proves

instance : Proves (Set (Bₐ.Formula V)) (Bₐ.Formula V) where
  proves X α := ∃ n, Nonempty (Proof X α n)

instance : Proves (Set (Bₐ.Formula V)) (Set (Bₐ.Formula V)) where
  proves X Y := ∀ α ∈ Y, X |~ α

example {p q : Bₐ.Formula V} : is_proof ![p, q, p ⟶ q ⟶ p ⋏ q, q ⟶ p ⋏ q, p ⋏ q] {p, q}
  | 0 => Or.inl (Set.mem_union_left _ (Set.mem_insert _ _))
  | 1 => Or.inl (Set.mem_union_left _  (Set.mem_insert_iff.mpr
    (Or.inr (Set.mem_singleton_iff.mpr rfl))))
  | 2 => Or.inl (Set.mem_union_right _ (Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_right _ ⟨p, q, rfl⟩))))
  | 3 => Or.inr ⟨0, Nat.le.step (Nat.le.step Nat.le.refl), 2, Nat.le.refl, rfl⟩
  | 4 => Or.inr ⟨1, Nat.le.step (Nat.le.step Nat.le.refl), 3, Nat.le.refl, rfl⟩

/-- Theorem 6.1: Induction principle for `|~`. -/
theorem Hilbert.induction (P : Bₐ.Formula V → Prop) (ho : ∀ α ∈ X ∪ Λ, P α)
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

/-- Soundness of `|~`. Equivalently, `|~ ⊆ ⊨`. -/
theorem soundness (h : X |~ α) : X ⊨ α := by
  have ⟨n, ⟨p⟩⟩ := h
  refine' Hilbert.induction (X ⊨ ·)
    (fun α hα => Or.elim hα
      (fun hαX _ hw => hw α hαX)
      (fun hαΛ w _ => _))
    (fun _ _ hα hαβ w hw => w.satisfies_arrow.mp (hαβ w hw) (hα w hw))
    p
  · simp only [Set.mem_union] at hαΛ
    refine' mem_Λ
      (fun ⟨α, β, γ, h₁⟩ => _)
      (fun ⟨α, β, h₂⟩ => _)
      (fun h₃ => _)
      (fun ⟨α, β, h₄⟩ => _)
      hαΛ
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
    · simp_rw [← h₄, Model.satisfies_arrow]
      intro hαβ hβ
      simp only [Model.satisfies_not]
      exact fun hα => w.satisfies_not.mp (hαβ hα) hβ

end Hilbert
