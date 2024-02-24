import Mathlib.Data.Set.Basic

namespace Set

theorem ssubset_exists_mem_not_mem {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset_iff_exists_mem_not_mem.mp (ssubset_def ▸ h).right

end Set
