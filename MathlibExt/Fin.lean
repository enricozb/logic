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

end Fin
