import Mathlib.Data.Set.Finite

namespace Set

theorem ssubset_exists_mem_not_mem {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset_iff_exists_mem_not_mem.mp (ssubset_def ▸ h).right

/-- Maps a set of pairs to the set of elements in the pairs, `{(aᵢ, bᵢ)}ᵢ ↦ {aᵢ}ᵢ ∪ {bᵢ}ᵢ`. -/
abbrev flatten (s : Set (M × M)) : Set M := (Prod.fst '' s) ∪ (Prod.snd '' s)

theorem flatten_subset {s₁ s₂ : Set (M × M)} (h : s₁ ⊆ s₂) : s₁.flatten ⊆ s₂.flatten := by
  intro x hx
  refine' Or.elim hx (fun hx₁ => _) (fun hx₂ => _)
  · have ⟨⟨a, b⟩, hab, ha⟩ := hx₁
    simp only [← ha, mem_union, mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact Or.inl ⟨b, h hab⟩
  · have ⟨⟨a, b⟩, hab, hb⟩ := hx₂
    simp only [← hb, mem_union, mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact Or.inr ⟨a, h hab⟩

theorem flatten_finite {s : Set (M × M)} (h : s.Finite) : s.flatten.Finite := by
  simp only [finite_union]
  exact finite_image_fst_and_snd_iff.mpr h

end Set
