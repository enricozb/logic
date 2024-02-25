import Mathlib.Data.Set.Finite
import Mathlib.Order.Chain

/-- A finite subset of some chain has a maximum. -/
theorem Chain.fin_subset_max
    {α : Sort _} {K : Set (Set α)} {U₀ : Set α}
    (hKne : K.Nonempty) (hKc : IsChain (· ⊆ ·) K) (hU₀fin : U₀.Finite)
    (map : ∀ aᵢ ∈ U₀, ∃ Yᵢ ∈ K, aᵢ ∈ Yᵢ) : ∃ Y ∈ K, U₀ ⊆ Y := by
  induction U₀, hU₀fin using Set.Finite.dinduction_on with
  | H0 => exact ⟨hKne.choose, hKne.choose_spec, Set.empty_subset _⟩
  | @H1 αₙ U₀' _ _ ih =>
    have ⟨Yₙ, hYₙmemK, hαₙmemYₙ⟩ := map αₙ (Set.mem_insert _ _)
    have ⟨Y', hY'memK, hY'sup⟩ := ih (fun a ha => map a (Set.mem_insert_of_mem _ ha))
    obtain rfl | hne := eq_or_ne Yₙ Y'
    · exact ⟨Yₙ, hYₙmemK, Set.insert_subset hαₙmemYₙ hY'sup⟩
    · cases hKc hY'memK hYₙmemK hne.symm with
      | inl h => exact ⟨Yₙ, hYₙmemK, Set.insert_subset hαₙmemYₙ (hY'sup.trans h)⟩
      | inr h => exact ⟨Y', hY'memK, Set.insert_subset (h hαₙmemYₙ) hY'sup⟩
