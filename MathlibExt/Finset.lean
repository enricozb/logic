import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic

namespace Finset

variable [DecidableEq α]

def iUnion [DecidableEq α] (t : Fin n → Finset α) : Finset α :=
  match n with
  | 0 => {}
  | 1 => t 0
  | _+1 => (t 0) ∪ (Finset.iUnion (Fin.tail t))

theorem iUnion_mem {t : Fin n → Finset α} : a ∈ Finset.iUnion t ↔ ∃ i, a ∈ t i := by sorry

end Finset
