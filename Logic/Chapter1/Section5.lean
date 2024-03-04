import «MathlibExt».Finset
import «MathlibExt».Set
import «Logic».Chapter1.Section4

open Notation

/- Every set M can be (totally) ordered. -/
section TotallyOrdered

variable {V : Type _} [DecidableEq V] {S : Signature} [Interpretation S]

def Model.value_subtype {P : V → Prop} (w : Model V) (α : S.Formula {v // P v}) : Bool :=
  let w₀ : Model {v // P v} := ⟨fun v => w.valuation v.val⟩
  w₀.value α

instance {P : V → Prop} : Satisfies (Model V) (S.Formula {v // P v}) where
  satisfies w α := w.value_subtype α

instance {P : V → Prop} : Satisfies (Model V) (Set (S.Formula {v // P v})) where
  satisfies w X := ∀ α ∈ X, w ⊨ α

namespace Signature

/--
  If a formula's variable type is a subtype `{v : V // P v}`, it can be embedded into the type of
  formulas whose variable type is the carrier `V`.
-/
def Formula.supertype_embed {P : V → Prop} (α : S.Formula {v // P v}) : S.Formula V :=
  match α with
  | .var v => .var ↑v
  | .app a s φs => .app a s (fun i => (φs i).supertype_embed)

instance {P : V → Prop} : CoeOut (S.Formula {v // P v}) (S.Formula V) where
  coe α := α.supertype_embed

instance {P : V → Prop} : CoeOut (Set (S.Formula {v // P v})) (Set (S.Formula V)) where
  coe X := {↑α | α ∈ X}

/-- The set of all variables in a formula. -/
def Formula.vars (α : S.Formula V) : Set V :=
  match α with
  | .var v => {v}
  | .app a _ φs => ⋃ (i : Fin a), (φs i).vars

theorem Formula.vars_var : (.var v : S.Formula V).vars = {v} := rfl

theorem Formula.vars_and {α β : Bₐ.Formula V} :
    (α ⋏ β).vars = α.vars ∪ β.vars := by
  simp only [Formula.vars, Set.ext_iff, Set.mem_iUnion, Set.mem_union, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, implies_true]

theorem Formula.vars_or {α β : Bₐ.Formula V} :
    (α ⋎ β).vars = α.vars ∪ β.vars := by
  simp only [Formula.vars, Set.ext_iff, Set.mem_iUnion, Set.mem_union,
    Fin.exists_fin_one, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, implies_true]

theorem Formula.vars_arrow {α β : Bₐ.Formula V} :
    (α ⟶ β).vars = α.vars ∪ β.vars := by
  simp only [Formula.vars, Set.ext_iff, Set.mem_iUnion, Set.mem_union,
    Fin.exists_fin_one, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, implies_true]

theorem Formula.vars_finite (α : S.Formula V) : α.vars.Finite := by
  match α with
  | .var v => simp only [vars, Set.finite_singleton]
  | .app _ _ φs => exact Set.finite_iUnion (fun i => (φs i).vars_finite)

def set_vars (X : Set (S.Formula V)) : Set V := ⋃₀ (Formula.vars '' X)

theorem set_vars_finite {X : Set (S.Formula V)} (h : X.Finite) : (set_vars X).Finite := by
  simp only [set_vars]
  refine' Set.Finite.sUnion (Set.Finite.image _ h) _
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun α _ => α.vars_finite

theorem vars_subset_set_vars {X : Set (S.Formula V)} {α : S.Formula V} (h : α ∈ X) :
    α.vars ⊆ set_vars X :=
  Set.subset_sUnion_of_mem (Set.mem_image_of_mem _ h)

end Signature

theorem total_preorder_fin (n : ℕ) : ∃ r, IsTotalPreorder (Fin n) r := ⟨(· ≤ ·), by infer_instance⟩

theorem total_preorder_finite (h : Finite M) : ∃ r, IsTotalPreorder M r := by
  have ⟨n, ⟨f, _, _, _⟩⟩ := h.exists_equiv_fin
  have ⟨r, hr⟩ := total_preorder_fin n
  let r' m₁ m₂ := r (f m₁) (f m₂)
  have htrans : IsTrans M r' := ⟨fun a b c => hr.1.1 (f a) (f b) (f c)⟩
  have htotal : IsTotal M r' := ⟨fun a b => hr.2.1 (f a) (f b)⟩
  exact ⟨r', ⟨⟩⟩

/--
  Every set M can be (totally) ordered.

  This is an application of the propositional compactness theorem.
-/
theorem total_preorder (M : Sort _) : ∃ r, IsTotalPreorder M r := by
  wlog hM : ∃ _ : M, True
  · have hM : Finite M := by
      by_contra h
      simp only [not_finite_iff_infinite, not_exists, not_true_eq_false] at h hM
      exact hM (Infinite.nonempty M).some
    exact total_preorder_finite hM
  haveI : Inhabited M := ⟨hM.choose⟩

  let X : Set (Bₐ.Formula (M × M)) :=
    {.var (a, b) ⋏ .var (b, c) ⟶ .var (a, c) | (a : M) (b : M) (c : M)} ∪
    {.var (a, b) ⋎ .var (b, a) | (a : M) (b : M)}

  suffices hX : satisfiable_set X
  · have ⟨w, hw⟩ := hX
    let r a b := w ⊨ (.var (a, b) : Bₐ.Formula (M × M))
    haveI htrans : IsTrans M r := by
      refine' ⟨fun a b c => _⟩
      have : .var (a, b) ⋏ .var (b, c) ⟶ .var (a, c) ∈ X := by
        exact Set.mem_union_left _ ⟨a, b, c, rfl⟩
      have htrans := hw _ this
      rw [Model.satisfies_arrow, Model.satisfies_and, and_imp] at htrans
      exact htrans
    haveI htotal : IsTotal M r := by
      refine' ⟨fun a b => _⟩
      have : .var (a, b) ⋎ .var (b, a) ∈ X := by exact Set.mem_union_right _ ⟨a, b, rfl⟩
      have htotal := hw _ this
      rw [Model.satisfies_or] at htotal
      exact htotal
    exact ⟨r, ⟨⟩⟩

  refine' Satisfies.compactness fun X₀ hX₀s hX₀f => _

  let M₁ := (Signature.set_vars X₀).flatten
  let X₁ := {α ∈ X | α.vars.flatten ⊆ M₁}

  have hX₀sX₁: X₀ ⊆ X₁ :=
    fun α hα => ⟨hX₀s hα, Set.flatten_subset (Signature.vars_subset_set_vars hα)⟩

  suffices hX₁ : satisfiable_set X₁
  · have ⟨w, hw⟩ := hX₁
    exact ⟨w, fun α hα => hw _ (hX₀sX₁ hα)⟩

  have hM₁f : M₁.Finite := Set.flatten_finite (Signature.set_vars_finite hX₀f)

  have ⟨r₁, hr₁⟩ := total_preorder_finite hM₁f.to_subtype
  haveI hr₁trans : IsTrans M₁ r₁ := hr₁.1
  haveI hr₁total : IsTotal M₁ r₁ := hr₁.2

  haveI {a b} : Decidable (a ∈ M₁ ∧ b ∈ M₁) := Classical.dec _
  haveI : DecidableRel r₁ := Classical.decRel _

  let w₁ : Model (M × M) := ⟨
    fun ⟨a, b⟩ =>
      if h : a ∈ M₁ ∧ b ∈ M₁ then
        r₁ ⟨a, h.left⟩ ⟨b, h.right⟩
      else
        false
  ⟩
  refine' ⟨w₁, fun α ⟨hα, hαvars⟩ => Or.elim hα (fun ⟨a, b, c, hαt⟩ => _) (fun ⟨a, b, hαs⟩ => _)⟩

  -- trans
  · have habc : {a, b, c} ⊆ α.vars.flatten := by
      simp_rw [← hαt, Signature.Formula.vars_arrow, Signature.Formula.vars_and,
        Signature.Formula.vars_var, Set.union_singleton, Set.flatten, Set.image]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left,
        or_self_left]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      refine' Or.elim hv (fun hva => _) (Or.elim · (fun hvb => _) (fun hvc => _))
      · exact Or.inl (Or.inl hva.symm)
      · exact Or.inr (Or.inr hvb.symm)
      · exact Or.inr (Or.inl hvc.symm)
    have ha : a ∈ M₁ := by
      refine' habc.trans hαvars _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
    have hb : b ∈ M₁ := by
      refine' habc.trans hαvars _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
    have hc : c ∈ M₁ := by
      refine' habc.trans hαvars _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
    simp only [← hαt, Model.satisfies_arrow, Model.satisfies_and, Model.satisfies_var,
      dif_pos (And.intro ha hb), dif_pos (And.intro hb hc), dif_pos (And.intro ha hc),
      decide_eq_true_eq, and_imp]
    exact hr₁.1.1 ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩

  -- symm
  · have hab : {a, b} ⊆ α.vars.flatten := by
      simp_rw [← hαs, Signature.Formula.vars_or, Signature.Formula.vars_var, Set.union_singleton,
        Set.flatten, Set.image]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      exact Or.elim hv (fun ha => Or.inl (Or.inr ha.symm)) (fun hb => Or.inl (Or.inl hb.symm))
    have ha : a ∈ M₁ := hab.trans hαvars (Set.mem_insert a {b})
    have hb : b ∈ M₁ := hab.trans hαvars (Set.mem_insert_of_mem a rfl)
    simp only [← hαs, Model.satisfies_or, Model.satisfies_var,
      dif_pos (And.intro ha hb), dif_pos (And.intro hb ha), decide_eq_true_eq]
    exact hr₁.2.1 ⟨a, ha⟩ ⟨b, hb⟩

end TotallyOrdered
