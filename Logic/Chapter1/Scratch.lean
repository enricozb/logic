import Mathlib.Data.Set.Finite
import Mathlib.Order.Chain
import Mathlib.Data.Set.Card

variable
  {α : Sort _} {K : Set (Set α)}
  (hKc : IsChain (· ⊆ ·) K) (U₀ : Set α) (hU₀fin : Set.Finite U₀)
  (hKne : Set.Nonempty K)
  (map : ∀ αᵢ ∈ U₀, ∃ Yᵢ ∈ K, αᵢ ∈ Yᵢ)

theorem chain_fin_subset_max : ∃ Y ∈ K, U₀ ⊆ Y := by
  induction' h : Set.ncard U₀ with n n_ih generalizing U₀
  · rw [Set.ncard_eq_zero hU₀fin] at h
    rw [h]
    have ⟨Y, hY⟩ := hKne
    exact ⟨Y, hY, Set.empty_subset Y⟩

  · have ⟨αₙ, U₀', hαₙnotin, hαₙinsert, hU₀'card⟩ := Set.eq_insert_of_ncard_eq_succ h
    have hαₙ : αₙ ∈ U₀ := by rw [←hαₙinsert]; exact Set.mem_insert _ _
    have hαₙinsert_sub : insert αₙ U₀' ⊆ U₀ := by rw [hαₙinsert]
    have hU₀'sub : U₀' ⊂ U₀ := Set.ssubset_iff_insert.mpr ⟨αₙ, hαₙnotin, hαₙinsert_sub⟩
    have hU₀'fin : Set.Finite U₀' := Set.Finite.subset hU₀fin hU₀'sub.left
    have map' : ∀ αᵢ ∈ U₀', ∃ Yᵢ ∈ K, αᵢ ∈ Yᵢ := by
      intro αᵢ hαᵢ
      exact map αᵢ (Set.mem_of_subset_of_mem hU₀'sub.left hαᵢ)
    have ⟨Y', hY'memK, hY'sup⟩ := n_ih U₀' hU₀'fin map' hU₀'card
    have ⟨Yₙ, hYₙmemK, hαₙmemYₙ⟩ := map αₙ hαₙ

    wlog hneq : Y' ≠ Yₙ
    · simp only [ne_eq, not_not] at hneq
      apply Exists.intro Y'
      apply And.intro hY'memK
      intro αᵢ hαᵢ
      simp [←hαₙinsert] at hαᵢ
      match hαᵢ with
      | Or.inl hαᵢeqαₙ => rw [hαᵢeqαₙ, hneq]; exact hαₙmemYₙ
      | Or.inr hαᵢmemU₀' => exact hY'sup hαᵢmemU₀'

    apply Or.elim (hKc hY'memK hYₙmemK hneq)
    · intro hY'subYₙ
      suffices hU₀subYₙ : U₀ ⊆ Yₙ
      · exact ⟨Yₙ, hYₙmemK, hU₀subYₙ⟩
      intro αᵢ hαᵢ
      simp [←hαₙinsert] at hαᵢ
      match hαᵢ with
      | Or.inl hαᵢeqαₙ => rw [hαᵢeqαₙ]; exact hαₙmemYₙ
      | Or.inr hαᵢmemU₀' => exact hY'subYₙ (hY'sup hαᵢmemU₀')

    · intro hYₙsub
      apply Exists.intro Y'
      apply And.intro hY'memK
      intro αᵢ hαᵢ
      simp [←hαₙinsert] at hαᵢ
      match hαᵢ with
      | Or.inl hαᵢeqαₙ => rw [hαᵢeqαₙ]; exact hYₙsub hαₙmemYₙ
      | Or.inr hαᵢmemU₀' => exact hY'sup hαᵢmemU₀'

