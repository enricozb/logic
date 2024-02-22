import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PNat.Defs
import «MathlibExt».Fin
import «Logic».Chapter1.Notation

open Notation

section Signature

/-- A propositional signature is made up of sets of symbols for each arity `n ∈ ℕ`. -/
structure Signature where
  /-- For each arity `n`, a set of symbols. -/
  symbols : ℕ → Type _

/-- Propositional formulas of a signature with a set `V` of _propositional variables_. -/
inductive Signature.Formula (S : Signature) (V : Type _) where
  /-- Variables. -/
  | var (v : V) : S.Formula V
  /-- Function application. -/
  | app (a : ℕ) (s : S.symbols a) (φs : [S.Formula V; a]) : S.Formula V

/--
  The (boolean) interpretation of a signature `S` is an assignment of boolean functions of
  appropriate arity to each symbol in `S`.

  This is also called a _structure_ in some literatures.
-/
class Interpretation (S : Signature) where
  fns : ∀ {n}, S.symbols n → 𝔹 n

end Signature


section Model

/--
  A model, or _valuation_ which, in the case of boolean signatures, is a map from propositional
  variables to `Bool`.
-/
structure Model (V : Type _) where
  valuation : V → Bool

variable {S : Signature} [I : Interpretation S]

/-- The value of a formula with `n` unbound variables given a model. -/
def Model.value (w : Model V) (α : S.Formula V) : Bool :=
  match α with
  | .var p => w.valuation p
  | .app _ s φs => I.fns s (fun i => w.value (φs i))

instance : Tilde (Model V) where tilde w := ⟨fun v => ~ (w.valuation v)⟩

/--
  A formula `α` (with a finite number of variables) represents a boolean function `f : 𝔹 n` if they
  are equal under all models.
-/
def Signature.Formula.represents (α : S.Formula (Fin n)) (f : 𝔹 n) : Prop :=
  ∀ (w : Model (Fin n)), w.value α = f w.valuation

/-- A boolean formula `α` (with a finite number of variables) has an associated boolean function. -/
def Signature.Formula.function (α : S.Formula (Fin n)) : 𝔹 n := (fun b => (Model.mk b).value α)

/-- A boolean formula `α` (with a finite number of variables) represents it's boolean function. -/
theorem Signature.Formula.represents_function (α : S.Formula (Fin n)) : α.represents α.function :=
  fun _ => rfl

/--
  A boolean signature.

  This is a class since multiple signatures can represent boolean formulas "faithfully". That is,
  the symbols have their expected interpretations. For example, the properties of `{¬, ∧}`,
  `{¬, ∨}`, and `{¬, ∧, ∨}` should roughly be equivalent, since these signatures represent the same
  set of boolean functions, and their respective (possibly abbreviated) symbols are equivalent.
-/
class Signature.Boolean (S : Signature) [Interpretation S] (V : Type _) where
  tilde : Tilde (S.Formula V) := by infer_instance
  wedge : Wedge (S.Formula V) := by infer_instance
  vee : Vee (S.Formula V) := by infer_instance
  not : ∀ (w : Model V) (α : S.Formula V), w.value (~α) = !w.value α
  and : ∀ (w : Model V) (α β : S.Formula V), w.value (α ⋏ β) = (w.value α && w.value β)
  or : ∀ (w : Model V) (α β : S.Formula V), w.value (α ⋎ β) = (w.value α || w.value β)
  induction (P : S.Formula V → Prop)
    (var : ∀ v, P (.var v))
    (not : ∀ α, P α → P (~α))
    (and : ∀ α β, P α → P β → P (α ⋏ β))
    (or : ∀ α β, P α → P β → P (α ⋎ β))
    (φ : S.Formula V) : P φ

instance [B : S.Boolean V] : Tilde (S.Formula V) := B.tilde
instance [B : S.Boolean V] : Wedge (S.Formula V) := B.wedge
instance [B : S.Boolean V] : Vee (S.Formula V) := B.vee
instance [S.Boolean V] [I : Inhabited V] : Bot (S.Formula V) := ⟨.var I.default ⋏ ~.var I.default⟩
instance [S.Boolean V] [Inhabited V] : Top (S.Formula V) := ⟨~⊥⟩

variable {V : Type _} [Inhabited V] (S : Signature) [Interpretation S] [S.Boolean V] (w : Model V)

@[simp] theorem Model.value_and (α β : S.Formula V) :
    w.value (α ⋏ β) = Bool.and (w.value α) (w.value β) := by
  simp only [Signature.Boolean.and]

@[simp] theorem Model.value_or (α β : S.Formula V) :
    w.value (α ⋎ β) = Bool.or (w.value α) (w.value β) := by
  simp only [Signature.Boolean.or]

@[simp] theorem Model.value_not (α : S.Formula V) : w.value (~α) = Bool.not (w.value α) := by
  simp only [Signature.Boolean.not]

@[simp] theorem Model.value_bot : w.value (⊥ : S.Formula V) = false := by
  simp only [Bot.bot, value_and, value_not, Bool.and_not_self]

@[simp] theorem Model.value_top : w.value (⊤ : S.Formula V) = true := by
  simp only [Top.top, value_or, value_not, value_bot, Bool.not_false]

@[simp] theorem Model.value_ite (b : Bool) (α β : S.Formula V) :
    w.value (if b then α else β) = if b then w.value α else w.value β := by
  by_cases h : b
  · simp_rw [if_pos h]
  · simp_rw [if_neg h]

@[simp] theorem Model.value_bigwedge {n : ℕ} (φs : [S.Formula V; n + 1]) :
    w.value (⋀ φs) = ⋀ (fun i => w.value (φs i)) := by
  match n with
  | 0 => rfl
  | n+1 => simp_rw [BigWedge.apply, value_and, value_bigwedge, Wedge.wedge, Fin.init, Fin.init_def]

@[simp] theorem Model.value_bigvee {n : ℕ} (φs : [S.Formula V; n + 1]) :
    w.value (⋁ φs) = ⋁ (fun i => w.value (φs i)) := by
  match n with
  | 0 => rfl
  | n+1 => simp_rw [BigVee.apply, value_or, value_bigvee, Vee.vee, Fin.init, Fin.init_def]

end Model

section Boolean

inductive B.Unary | not
inductive B.Binary | and | or

/- The common boolean signature `{¬, ∨, ∧}`. -/
def B : Signature := ⟨fun | 1 => B.Unary | 2 => B.Binary | _ => Empty⟩

/-- The common interpretation of `{¬, ∨, ∧}`. -/
instance : Interpretation B where
  fns := fun {n} => match n with
    | 1 => fun
      | .not => fun b => Bool.not (b 0)
    | 2 => fun
      | .and => fun b => Bool.and (b 0) (b 1)
      | .or  => fun b => Bool.or  (b 0) (b 1)
    | 0 | _+3 => fun _ => by contradiction

instance : Tilde (B.Formula V) := ⟨fun α => .app 1 .not ![α]⟩
instance : Wedge (B.Formula V):= ⟨fun α β => .app 2 .and ![α, β]⟩
instance : Vee (B.Formula V) := ⟨fun α β => .app 2 .or ![α, β]⟩

theorem B.induction {P : B.Formula V → Prop}
    (var : ∀ v, P (.var v))
    (not : ∀ α, P α → P (~α))
    (and : ∀ α β, P α → P β → P (α ⋏ β))
    (or : ∀ α β, P α → P β → P (α ⋎ β))
    (φ : B.Formula V) : P φ := by
  match φ with
  | .var v => exact var v
  | .app 1 .not φs =>
    simp only [Tilde.tilde, Fin.Tuple.literal_1 φs] at not
    rw [← Fin.Tuple.literal_1 φs]
    exact not _ (B.induction var not and or (φs 0))
  | .app 2 .and φs =>
    simp only [Wedge.wedge, Fin.Tuple.literal_2 φs] at and
    rw [← Fin.Tuple.literal_2 φs]
    exact and _ _ (B.induction var not and or (φs 0)) (B.induction var not and or (φs 1))
  | .app 2 .or φs =>
    simp only [Vee.vee, Fin.Tuple.literal_2 φs] at or
    rw [← Fin.Tuple.literal_2 φs]
    exact or _ _ (B.induction var not and or (φs 0)) (B.induction var not and or (φs 1))

instance {V : Type _} : Signature.Boolean B V where
  not := by simp only [Model.value, Interpretation.fns, Matrix.cons_val_fin_one, implies_true]
  and := by simp only [Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, implies_true]
  or := by simp only [Model.value, Interpretation.fns, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, implies_true]
  induction P var not and or φ := B.induction var not and or φ

/-- Boolean formulas with at most `n` variables. -/
notation "𝓕" n => B.Formula (Fin n)

end Boolean

namespace Exercises

inductive L.Constant | true | false
inductive L.Binary | and | xor

/--
  The signature of linear functions, `{⊤, ⊥, ¬, ∧, ⊕}`, where `⊕` is exclusive or.
-/
def L : Signature := ⟨fun | 0 => L.Constant | 1 => B.Unary | 2 => L.Binary | _ => Empty⟩

instance : Tilde (L.Formula V) := ⟨fun α => .app 1 .not ![α]⟩
instance : Wedge (L.Formula V) := ⟨fun α β => .app 2 .and ![α, β]⟩
instance : Oplus (L.Formula V) := ⟨fun α β => .app 2 .xor ![α, β]⟩
instance : Top (L.Formula V) := ⟨.app 0 .true ![]⟩
instance : Bot (L.Formula V) := ⟨.app 0 .false ![]⟩

instance : Interpretation L where
  fns := fun {n} => match n with
    | 0 => fun
      | .true  => fun _ => Bool.true
      | .false => fun _ => Bool.false
    | 1 => fun
      | .not => fun b => Bool.not (b 0)
    | 2 => fun
      | .and => fun b => Bool.and (b 0) (b 1)
      | .xor => fun b => Bool.xor (b 0) (b 1)
    | _+3 => fun _ => by contradiction

def is_linear (α : L.Formula (Fin n)) (c : [L.Constant; n + 1]) :=
  α = ⨁ (fun (i : Fin (n + 1)) => match i with
    | 0 => .app 0 (c 0) ![]
    | k@⟨i + 1, h⟩ => (.app 0 (c k) ![]) ⋏ .var ⟨i, Nat.succ_lt_succ_iff.mp h⟩
  )

/--
  A function `f : 𝔹 n` is linear if it is represented by a formula of the form
  `f(x₁, .., xₙ) = a₀ + (a₁ ∧ x₁) + .. + (aₙ ∧ xₙ)`, for some constants `aᵢ`.
-/
class IsLinear (f : 𝔹 n) where
  α : L.Formula (Fin n)
  represents : α.represents f
  constants : [L.Constant; n + 1]
  linear : is_linear α constants

/-- Exercise 1a: The representation of linear functions is unique. -/
proof_wanted linear_is_unique (l₁ l₂ : IsLinear f) : l₁.constants = l₂.constants

/-- Exercise 2: A compound boolean formula `φ` is either of the form `¬α`, `α ⋏ β`, or `α ⋎ β`. -/
proof_wanted compound_formula {φ : B.Formula V} (_ : ∀ p, φ ≠ .var p) :
    (∃ α, φ = ~α) ∨ (∃ α β, φ = α ⋏ β) ∨ (∃ α β, φ = α ⋎ β)

/- Exercises 3-4 aren't really statable as they represent formulas as strings. -/

end Exercises
