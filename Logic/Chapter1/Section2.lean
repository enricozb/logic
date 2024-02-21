import Mathlib.Data.FinEnum
import «MathlibExt».Bool
import «MathlibExt».Fin
import «Logic».Chapter1.Notation
import «Logic».Chapter1.Section1

open Notation

instance : FinEnum Bool := FinEnum.ofList [false, true] (fun b => by
  simp_rw [List.mem_cons, List.not_mem_nil, or_false, Bool.dichotomy])

/- Definition and statements about semantic equivalence of formulas. -/
section SemanticEquivalence

variable {S₁ S₂ : Signature} [Interpretation S₁] [Interpretation S₂]

/--
  Heterogeneous Semantic Equivalence: Two formulas (of possibly different signatures) are
  semantically equivalent if they have the same valuation for all models.
-/
def semeq' (α : S₁.Formula V) (β : S₂.Formula V) :=
  ∀ w : Model V, w.value α = w.value β

scoped[Notation] infix:67 " ≡' " => semeq'

@[simp] theorem semeq'_represents {α : S₁.Formula (Fin n)} {β : S₂.Formula (Fin n)} {f : 𝔹 n}
    (hs : α ≡' β) (hr : α.represents f) : β.represents f := by
  intro w
  rw [← hr w, hs w]

variable {V : Type _} {S : Signature} [Interpretation S]

/--
  Homogenous Semantic Equivalence: Two formulas of the same signature are semantically equivalent
  if they have the same valuation for all models.
-/
def semeq (α β : S.Formula V) := semeq' α β

scoped[Notation] infix:67 " ≡ " => semeq

@[simp] theorem semeq_def {α β : S.Formula V} : α ≡ β ↔ ∀ w : Model V, w.value α = w.value β := by
  rfl

/-- `≡` is an equivalence relation when comparing formulas of the same signature. -/
instance : Equivalence (@semeq V S _) where
  refl := by simp only [semeq, semeq', implies_true]
  symm := by intro φ₁ φ₂ h w; exact (h w).symm
  trans := by intro φ₁ φ₂ φ₃ h₁ h₂ w; rw [h₁ w, h₂ w]

theorem semeq_refl {α : S.Formula V} : α ≡ α := instEquivalenceFormulaSemeq.refl α
theorem semeq_symm {α β : S.Formula V} : α ≡ β → β ≡ α := instEquivalenceFormulaSemeq.symm
theorem semeq_trans {α β χ: S.Formula V} : α ≡ β → β ≡ χ → α ≡ χ :=
  instEquivalenceFormulaSemeq.trans

/-- `≡` is a _congruence relation_ in `B`. -/
theorem semeq_congr {α α' β β' : B.Formula V} (hα : α ≡ α') (hβ : β ≡ β') :
    (α ⋏ β ≡ α' ⋏ β') ∧ (α ⋎ β ≡ α' ⋎ β') ∧ (~α ≡ ~α') := by
  simp only [semeq_def, hα _, hβ _, Model.value_and, Model.value_or, Model.value_not,
    implies_true, and_self]

/-- Example semantic equivalences for arbitrary propositional variables `V`. -/
example (α β : B.Formula V) :
  α ≡ ~~α ∧
  α ⋏ β ≡ β ⋏ α ∧
  α ⋎ β ≡ β ⋎ α ∧
  α ⋏ α ≡ α ∧
  α ⋎ α ≡ α ∧
  ~(α ⋏ β) ≡ ~α ⋎ ~β ∧
  ~(α ⋎ β) ≡ ~α ⋏ ~β
  := by
  simp only [semeq_def, Model.value_and, Model.value_or, Model.value_not, Bool.not_not,
    Bool.not_and, Bool.not_or, Bool.and_comm, Bool.and_self, Bool.or_comm, Bool.or_self,
    implies_true, and_self]

/-- Example semantic equivalences for inhabited propositional variables `V`. -/
example [Inhabited V] (α : B.Formula V) :
  α ⋎ ~α ≡ ⊤ ∧
  α ⋏ ~α ≡ ⊥ ∧
  α ⋏ ⊤  ≡ α ∧
  α ⋎ ⊥  ≡ α
  := by
  simp only [semeq_def, Model.value_and, Model.value_or, Model.value_not, Model.value_top,
    Model.value_bot, Bool.or_not_self, Bool.and_true, Bool.or_false, Bool.and_not_self,
    implies_true, and_self]

variable [DecidableEq (S.Formula V)]

/-- Substitutes instances of `α` with `β` in `φ`. -/
def subst (φ α β : S.Formula V) : S.Formula V :=
  if φ = α then
    β
  else
    match φ with
    | .var p => .var p
    | .app a s φs => .app a s (fun i => subst (φs i) α β)

/-- Notation for substitution. `φ[α ↦ β]` substitutes `α` with `β` in `φ`. -/
scoped[Notation] notation φ:max "[" α "↦" β "]" => subst φ α β

@[simp] theorem subst_self (α β : S.Formula V) : α[α ↦ β] = β := by
  unfold subst
  simp only [ite_true]

/--
  Substituting semantically equivalent formulas `α β` within a formula `φ`
  produces an equivalent formula.
-/
theorem semeq_of_susbst_semeq (α β φ : S.Formula V) (h : α ≡ β) : φ[α ↦ β] ≡ φ := by
  induction' φ with p a s φs φs_ih
  · by_cases hp : .var p = α
    · rw [subst, if_pos hp, hp]; exact semeq_symm h
    · rw [subst, if_neg hp]; exact semeq_refl

  · by_cases hφs : .app a s φs = α
    · rw [hφs, subst_self]; exact semeq_symm h
    · intro w
      simp only [subst, if_neg hφs, semeq, Model.value, Interpretation.fns, ←φs_ih _ w]

end SemanticEquivalence

section NormalForm

/-- The list of inputs that satisfy `f : 𝔹 n`. -/
def satisfying_inputs (f : 𝔹 n) : List [Bool; n] := (FinEnum.pi.enum (fun _ => Bool)).filter f

theorem mem_satisfying_inputs_iff (f : 𝔹 n) : b ∈ satisfying_inputs f ↔ f b = true := by
  simp only [satisfying_inputs, List.mem_filter, FinEnum.pi.mem_enum, true_and, imp_self]

theorem not_mem_satisfying_inputs_iff (f : 𝔹 n) : b ∉ satisfying_inputs f ↔ f b = false := by
  simp only [mem_satisfying_inputs_iff f, Bool.not_eq_true]

/-- A function `f : 𝔹 n` having no satisfying inputs implies it is false for all inputs. -/
theorem satisfying_inputs_empty_iff (f : 𝔹 n) : satisfying_inputs f = [] ↔ ∀ b, f b = false := by
  apply Iff.intro
  · intro h b
    simp only [← not_mem_satisfying_inputs_iff, h, List.not_mem_nil, not_false_eq_true]
  · intro hf
    simp only [satisfying_inputs, List.filter_eq_nil, hf _, not_false_eq_true, implies_true]

theorem bigand_value (φs : [B.Formula V; n + 1]) (w : Model V) :
    w.value (⋀ φs) = true ↔ ∀ i, w.value (φs i) = true := by
  match n with
  | 0 => simp only [BigWedge.bigwedge, foldop, Fin.forall_fin_one]
  | n + 1 =>
    have bigand_succ {n : ℕ} (φs : [B.Formula V; n + 1 + 1]) :
      ⋀ φs = (⋀ Fin.init φs) ⋏ (φs (Fin.last (n + 1))) := by rfl
    rw [bigand_succ φs]
    simp only [Model.value_and, bigand_value (Fin.init φs) w, Fin.init, Fin.forall_fin_succ',
      Bool.and_eq_true]

theorem bigor_value (φs : [B.Formula V; n + 1]) (w : Model V) :
    w.value (⋁ φs) = true ↔ ∃ i, w.value (φs i) = true := by
  match n with
  | 0 => simp only [BigVee.bigvee, foldop, (@Fin.exists_fin_one fun i => w.value (φs i)).symm]
  | n + 1 =>
    have bigor_succ {n : ℕ} (φs : [B.Formula V; n + 1 + 1]) :
      ⋁ φs = (⋁ Fin.init φs) ⋎ (φs (Fin.last (n + 1))) := by rfl
    rw [bigor_succ φs]
    simp only [Model.value_or, bigor_value (Fin.init φs) w, Fin.init, Fin.exists_fin_succ',
      Bool.or_eq_true]

section DNF

def dnf_entry (b : [Bool; n + 1]) : 𝓕 (n + 1) :=
  (⋀ fun i => if b i then .var i else ~(.var i))

/-- Disjunctive normal form. The DNF of a boolean function `f : 𝔹 n` is defined only for `n > 0`. -/
def dnf (f : 𝔹 (n + 1)) : 𝓕 (n + 1) :=
  let rec dnf' (inputs : List [Bool; n + 1]) :=
    match inputs with
    | [] => ⊥
    | b::bs => (dnf_entry b) ⋎ (dnf' bs)

  dnf' (satisfying_inputs f)

theorem model_value_bot {w : Model _} : w.value (⊥ : 𝓕 (n + 1)) = false := by
  simp only [Model.value, Interpretation.fns, Bool.and_not_self]

theorem model_value_cnf_entry (w : Model _) (b : [Bool; n + 1]) (i : Fin (n + 1)) :
    w.value (if b i = true then (.var i : 𝓕 (n + 1)) else ~(.var i)) = true ↔ w.valuation i = b i
    := by
  by_cases h : b i = true
  · simp only [h, if_pos h, Model.value]
  · simp only [h, if_neg h, Model.value, Interpretation.fns, Bool.not_eq_true']

theorem model_value_dnf_entry_eq_true_iff_eq (w : Model _) (b : [Bool; n + 1]) :
    w.value (dnf_entry b) = true ↔ w.valuation = b := by
  simp only [dnf_entry, bigand_value, model_value_cnf_entry]
  exact ⟨funext, congrFun⟩

theorem model_value_dnf_eq_true_iff_mem (w : Model _) (bs : List [Bool; n + 1]) :
    w.value (dnf.dnf' bs) = true ↔ w.valuation ∈ bs := by
  match bs with
  | [] => simp only [List.not_mem_nil, iff_false, Bool.not_eq_true, dnf.dnf', model_value_bot]
  | b::bs =>
    simp only [dnf.dnf', Model.value_or, Bool.or_eq_true, List.mem_cons]

    refine' ⟨
      fun h => h.elim
        (fun hw => Or.inl ((model_value_dnf_entry_eq_true_iff_eq w b).mp hw))
        (fun hw => Or.inr ((model_value_dnf_eq_true_iff_mem w bs).mp hw)),
      fun h => h.elim
        (fun hw => Or.inl ((model_value_dnf_entry_eq_true_iff_eq w b).mpr hw))
        (fun hw => Or.inr ((model_value_dnf_eq_true_iff_mem w bs).mpr hw))
      ⟩

theorem model_value_dnf_entry_self_eq_true {w : Model (Fin (n + 1))} :
    w.value (dnf_entry w.valuation) = true :=
  (model_value_dnf_entry_eq_true_iff_eq w w.valuation).mpr rfl

/-- Theorem 2.1a: Every boolean function of at least one variable is represented by its DNF. -/
theorem dnf_represents (f : 𝔹 (n + 1)) : (dnf f).represents f := by
  intro w

  match h : satisfying_inputs f with
  | [] => simp only [h, dnf, dnf.dnf', model_value_bot, (satisfying_inputs_empty_iff f).mp h]
  | b::bs =>
    simp only [h, dnf, dnf.dnf', Model.value_or]

    by_cases hw : w.valuation ∈ satisfying_inputs f
    · rw [(mem_satisfying_inputs_iff f).mp hw]
      apply Or.elim (List.mem_cons.mp (h ▸ hw))
      · intro hwb; simp_rw [← hwb, model_value_dnf_entry_self_eq_true, Bool.true_or]
      · intro hwbs; simp_rw [(model_value_dnf_eq_true_iff_mem w bs).mpr hwbs, Bool.or_true]

    · rw [(not_mem_satisfying_inputs_iff f).mp hw, Bool.or_eq_false_iff]
      rw [h, List.mem_cons.not, not_or] at hw
      have left := (model_value_dnf_entry_eq_true_iff_eq w b).not.mpr hw.left
      have right := (model_value_dnf_eq_true_iff_mem w bs).not.mpr hw.right
      rw [Bool.not_eq_true] at left right

      exact ⟨left, right⟩

end DNF

section CNF

def cnf_entry (b : [Bool; n + 1]) : 𝓕 (n + 1) :=
  (⋁ fun i => if b i then ~.var i else .var i)

/-- Conjunctive normal form. The CNF of a boolean function `f : 𝔹 n` is defined only for `n > 0`. -/
def cnf (f : 𝔹 (n + 1)) : 𝓕 (n + 1) :=
  let rec cnf' (inputs : List [Bool; n + 1]) :=
    match inputs with
    | [] => ⊤
    | b::bs => (cnf_entry b) ⋏ (cnf' bs)

  cnf' (satisfying_inputs (~f))

theorem tilde_bot {n : ℕ} : ~(⊥ : 𝓕 (n + 1)) ≡ ⊤ := by
    intro w
    simp only [Model.value, Interpretation.fns, Bool.not_and, Bool.not_not, Bool.or_comm]

theorem not_bigwedge (bs : [Bool; n + 1]) : (!⋀ bs) = ⋁ (fun i => !(bs i)) := by
  match n with
  | 0 => rfl
  | n + 1 => simp_rw [BigWedge.apply, Wedge.wedge, Bool.not_and, not_bigwedge (Fin.init bs),
    BigVee.apply, Vee.vee, Fin.init, Fin.init_def]

theorem cnf_entry_eq_not_dnf_entry {n : ℕ} (w : Model _) (b : [Bool; n + 1]) :
    w.value (cnf_entry b) = !(w.value (dnf_entry b)) := by
  simp only [cnf_entry, dnf_entry, Model.value_not, Model.value_bigwedge, Model.value_bigvee,
    Model.value_ite, not_bigwedge, Bool.not_ite, Bool.not_not]

theorem cnf'_semeq_not_dnf' {n : ℕ} (bs : List [Bool; n + 1]) : cnf.cnf' bs ≡ ~(dnf.dnf' bs) := by
  intro w
  match bs with
  | [] => simp only [cnf.cnf', dnf.dnf', tilde_bot w]
  | b::bs =>
    simp only [cnf.cnf', dnf.dnf', Model.value_and, Model.value_or, Model.value_not, Bool.not_or,
      cnf_entry_eq_not_dnf_entry, cnf'_semeq_not_dnf' bs w]

theorem cnf_semeq_not_dnf_not (f : 𝔹 (n + 1)) : cnf f ≡ ~(dnf (~f)) := by
  intro w

  match h : satisfying_inputs (~f) with
  | [] => simp only [h, cnf, cnf.cnf', dnf, dnf.dnf', tilde_bot _]
  | b::bs =>
    simp_rw [cnf, dnf, h, cnf.cnf', dnf.dnf', Model.value_and, Model.value_not, Model.value_or,
      Bool.not_or, ← cnf_entry_eq_not_dnf_entry w, ← Model.value_not, ← cnf'_semeq_not_dnf' bs _]

theorem represents_tilde {α : 𝓕 n} (h : α.represents f) : (~α).represents (~f) := by
  intro w
  simp_rw [Model.value_not, h w, Tilde.tilde, Function.comp]

/-- Theorem 2.1b: Every boolean function of at least one variable is represented by its CNF. -/
theorem cnf_represents (f : 𝔹 (n + 1)) : (cnf f).represents f := by
  have tilde_tilde (f : 𝔹 (n + 1)) : ~~f = f := by
    simp only [Tilde.tilde, Function.comp_def, Bool.not_not]

  intro w
  simp only [cnf_semeq_not_dnf_not f w,  tilde_tilde f ▸ represents_tilde (dnf_represents (~f)) w]

end CNF

/-- Corollary 2.2: Each formula of finite variables `φ` is equivalent to a DNF and a CNF. -/
theorem exists_dnf_cnf (φ : 𝓕 (n + 1)) : ∃ (f : 𝔹 (n + 1)), φ ≡ dnf f ∧ φ ≡ cnf f
    := by
  refine' ⟨φ.function, _, _⟩
  · intro w; rw [φ.represents_function, dnf_represents]
  · intro w; rw [φ.represents_function, cnf_represents]

end NormalForm


section FunctionalCompleteness

/--
  A signature is _functional complete_ if every boolean function (of at least one variable) has a
  reprentation.

  In keeping with the text, boolean functions of zero variables must be ignored. The signature
  `{¬, ∧, ∨}` cannot represent a boolean function of zero variables because formulas of zero
  variables do not exist, as there are no _prime_ formulas.
-/
def Signature.functional_complete (S : Signature) [Interpretation S] :=
  ∀ {n}, ∀ f : 𝔹 (n + 1), ∃ φ : S.Formula (Fin (n + 1)), φ.represents f

/-- `{¬, ∧, ∨}` is functional complete. -/
theorem B.functional_complete : B.functional_complete := by
  intro n f
  exact ⟨dnf f, dnf_represents _⟩

/-
  This section contains the two signatures `{¬, ∨}` and `{¬, ∧}` along with proofs of their
  functional completeness.
-/
section SmallerSignatures

inductive B.And | and
inductive B.Or | or

/-- The boolean signature `{¬, ∧}`. -/
def Bₐ : Signature := ⟨fun | 1 => B.Unary | 2 => B.And | _ => Empty⟩

instance : Tilde (Bₐ.Formula V) := ⟨fun α => .app 1 .not ![α]⟩
instance : Wedge (Bₐ.Formula V) := ⟨fun α β => .app 2 .and ![α, β]⟩
instance [I : Inhabited V] : Bot (Bₐ.Formula V) := ⟨.var I.default ⋏ ~.var I.default⟩
instance [Inhabited V] : Top (Bₐ.Formula V) := ⟨~⊥⟩

/-- The common interpretation of `{¬, ∧}`. -/
instance : Interpretation Bₐ where
  fns := fun {n} => match n with
    | 1 => fun .not => fun b => Bool.not (b 0)
    | 2 => fun .and => fun b => Bool.and (b 0) (b 1)
    | 0 | _+3 => fun _ => by contradiction

def Bₐ.of_B (α : B.Formula V) : Bₐ.Formula V :=
  match α with
  | .var v => .var v
  | .app 1 .not φs => ~ (Bₐ.of_B (φs 0))
  | .app 2 .and φs => Bₐ.of_B (φs 0) ⋏ Bₐ.of_B (φs 1)
  | .app 2 .or φs => ~ (~ Bₐ.of_B (φs 0) ⋏ ~ Bₐ.of_B (φs 1))

def Bₐ.of_B_represents (α : B.Formula V) : (Bₐ.of_B α) ≡' α := by
  intro w
  match α with
  | .var v => rfl
  | .app 1 .not φs =>
    simp only [of_B, Model.value, Interpretation.fns, Matrix.cons_val_fin_one,
      Bₐ.of_B_represents (φs 0) w]
  | .app 2 .and φs =>
    simp only [of_B, Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Bₐ.of_B_represents (φs 0) w, Bₐ.of_B_represents (φs 1) w]
  | .app 2 .or φs =>
    simp only [of_B, Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Bₐ.of_B_represents (φs 0) w, Bₐ.of_B_represents (φs 1) w, Bool.not_and,
      Bool.not_not]

theorem Bₐ.functional_complete : Bₐ.functional_complete := by
  intro n f
  refine' ⟨Bₐ.of_B (dnf f), _⟩
  intro w
  rw [of_B_represents _ w, dnf_represents]


/-- The boolean signature `{¬, ∨}`. -/
def Bₒ : Signature := ⟨fun | 1 => B.Unary | 2 => B.Or | _ => Empty⟩

instance : Tilde (Bₒ.Formula V) := ⟨fun α => .app 1 .not ![α]⟩
instance : Vee (Bₒ.Formula V) := ⟨fun α β => .app 2 .or ![α, β]⟩
instance [I : Inhabited V] : Top (Bₒ.Formula V) := ⟨.var I.default ⋎ ~.var I.default⟩
instance [Inhabited V] : Bot (Bₒ.Formula V) := ⟨~⊤⟩

/-- The common interpretation of `{¬, ∨}`. -/
instance : Interpretation Bₒ where
  fns := fun {n} => match n with
    | 1 => fun .not => fun b => Bool.not (b 0)
    | 2 => fun .or  => fun b => Bool.or  (b 0) (b 1)
    | 0 | _+3 => fun _ => by contradiction

def Bₒ.of_B (α : B.Formula V) : Bₒ.Formula V :=
  match α with
  | .var v => .var v
  | .app 1 .not φs => ~ (Bₒ.of_B (φs 0))
  | .app 2 .or φs => Bₒ.of_B (φs 0) ⋎ Bₒ.of_B (φs 1)
  | .app 2 .and φs => ~ (~ Bₒ.of_B (φs 0) ⋎ ~ Bₒ.of_B (φs 1))

def Bₒ.of_B_represents (α : B.Formula V) : (Bₒ.of_B α) ≡' α := by
  intro w
  match α with
  | .var v => rfl
  | .app 1 .not φs =>
    simp only [of_B, Model.value, Interpretation.fns, Matrix.cons_val_fin_one,
      Bₒ.of_B_represents (φs 0) w]
  | .app 2 .or φs =>
    simp only [of_B, Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Bₒ.of_B_represents (φs 0) w, Bₒ.of_B_represents (φs 1) w]
  | .app 2 .and φs =>
    simp only [of_B, Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Bₒ.of_B_represents (φs 0) w, Bₒ.of_B_represents (φs 1) w, Bool.not_or,
      Bool.not_not]

theorem Bₒ.functional_complete : Bₒ.functional_complete := by
  intro n f
  refine' ⟨Bₒ.of_B (dnf f), _⟩
  intro w
  rw [of_B_represents _ w, dnf_represents]

end SmallerSignatures

end FunctionalCompleteness
