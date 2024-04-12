import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation

namespace Fin

theorem exists_fin_succ' {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (.last _) :=
  ⟨fun ⟨i, h⟩ => lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h, fun h =>
    h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

theorem Tuple.literal_1 {α : Type _} (v : Fin 1 → α) : ![v 0] = v := by
  ext i
  simp only [Matrix.cons_val_fin_one, fin_one_eq_zero]

theorem Tuple.literal_2 {α : Type _} (v : Fin 2 → α) : ![v 0, v 1] = v := by
  ext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

-- a prefix of a sequence of length n of length k < n
def init' (q : Fin n → α) (h : n' < n) (i : Fin n') : α := q ⟨i.val, i.prop.trans h⟩

theorem init'_castLT (q : Fin n → α) (h : n' < n) (i : Fin n) (hi : i.val < n') :
    init' q h (i.castLT hi) = q i := rfl

theorem init'_coe (q : Fin n → α) (h : n' < n) (i : Fin n') :
    init' q h i = q ⟨i.val, i.prop.trans h⟩ := rfl

theorem append_last (a : Fin (m + 1) → α) (b : Fin (n + 1) → α) :
    Fin.append a b (Fin.last (m + 1 + n)) = b (Fin.last n) := by
  simp only [append, addCases, val_last, add_lt_iff_neg_left, subNat, coe_cast,
    add_tsub_cancel_left, eq_rec_constant]
  rfl

end Fin
