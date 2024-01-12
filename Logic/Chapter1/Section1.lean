import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.ScopedNS

namespace Chapter1
namespace Section1

/-- Vector notation. (eg. `[ Bool ; 3 ]`) -/
scoped[Chapter1.Section1] notation "[" α ";" n "]" => Fin n → α

/- Notation for formulas, and convenience notations such as `⋀`, `⋁`, etc. -/
namespace Notation

class Tee      (α : Sort _) where tee      : α
class Void     (α : Sort _) where void     : α
class Tilde    (α : Sort _) where tilde    : α → α
class Vee      (α : Sort _) where vee      : α → α → α
class Wedge    (α : Sort _) where wedge    : α → α → α
class Oplus    (α : Sort _) where oplus    : α → α → α

class BigVee   (α : Sort _) where bigvee   : ∀ {n}, [α; n + 1] → α
class BigWedge (α : Sort _) where bigwedge : ∀ {n}, [α; n + 1] → α
class BigOplus (α : Sort _) where bigoplus : ∀ {n}, [α; n + 1] → α

scoped[Chapter1.Section1.Notation] notation "⊤"    => Tee.tee
scoped[Chapter1.Section1.Notation] notation "⊥"    => Void.void
scoped[Chapter1.Section1.Notation] prefix:75 "~"   => Tilde.tilde
scoped[Chapter1.Section1.Notation] infixr:69 " ⋏ " => Wedge.wedge
scoped[Chapter1.Section1.Notation] infixr:68 " ⋎ " => Vee.vee
scoped[Chapter1.Section1.Notation] infixr:68 " ⊕ " => Oplus.oplus
scoped[Chapter1.Section1.Notation] prefix:75 "⋀"   => BigWedge.bigwedge
scoped[Chapter1.Section1.Notation] prefix:75 "⋁"   => BigVee.bigvee
scoped[Chapter1.Section1.Notation] prefix:75 "Σᵇ"  => BigOplus.bigoplus

/-- Convenience definition of big operators. -/
def bigop {a : ℕ} (op : α → α → α) (φs : [α; a+1]) :=
    match a with
    | 0 => φs 1
    | _+1 => op (φs 0) (bigop op (Fin.tail φs))

instance [Oplus α] : BigOplus α := ⟨bigop Oplus.oplus⟩
instance [Wedge α] : BigWedge α := ⟨bigop Wedge.wedge⟩
instance [Vee α]   : BigVee α   := ⟨bigop Vee.vee⟩

end Notation

open Notation

/--
  A boolean signature is made up of sets of symbols for each arity `n`.
-/
structure Signature where
  /-- For each arity `n`, a set of symbols. -/
  symbols : ℕ → Type u

/-- Formulas of a signature with at most `n` unbound variables. -/
inductive Signature.Formula {S: Signature} (n : ℕ) where
  /-- Variables. -/
  | var (i : Fin n) : Formula n
  /-- Function application. -/
  | app (a : ℕ) (s : S.symbols a) (φs : [S.Formula n; a]) : Formula n 

/--
  The interpretation of a set of symbols or formulas. Also called a
  _structure_ in some literatures.
-/
class Interpretation (𝓢 : Signature) where
  fns : ∀ {n}, 𝓢.symbols n → [Bool; n] → Bool

inductive Unary | not
inductive Binary | and | or

/-- The common boolean signature `{¬, ∨, ∧}`. -/
def 𝓑 : Signature := Signature.mk
  (fun | 1 => Unary | 2 => Binary | _ => Empty)

instance : Interpretation 𝓑 where
  fns := fun {n} => match n with
    | 1 => fun
      | .not => fun b => Bool.not (b 0)
    | 2 => fun
      | .and => fun b => Bool.and (b 0) (b 1)
      | .or  => fun b => Bool.or  (b 0) (b 1)
    | 0 | _+3 => fun _ => by contradiction

instance : Tilde (𝓑.Formula n) := ⟨fun φ => .app 1 .not ![φ]⟩
instance : Wedge (𝓑.Formula n) := ⟨fun φ₁ φ₂ => .app 2 .and ![φ₁, φ₂]⟩
instance : Vee (𝓑.Formula n) := ⟨fun φ₁ φ₂ => .app 2 .or ![φ₁, φ₂]⟩

/--
  A model, or _valuation_ which, in the case of boolean signatures, is just 
  a boolean vector.
-/
structure Model (n : ℕ) where
  vec : [Bool; n]

/-- The value of a formula with `n` unbound variables given a model. -/
def Model.value [I : Interpretation S] (w : Model n) (φ : S.Formula n) : Bool :=
  match φ with
  | .var i => w.vec i
  | .app _ s φs => I.fns s (fun i => w.value (φs i))

/--
  A boolean formula `φ` represents a boolean function `n` if they are equal
  under all valuations.
-/
def Signature.Formula.represents [I : Interpretation S] (φ : S.Formula n) (f : [Bool; n] → Bool) : Prop :=
  ∀ (w : Model n), w.value φ = f w.vec

namespace Exercises

inductive Constant | true | false
inductive Linear | and | xor

/--
  The boolean signature of linear functions, `{⊤, ⊥, ¬, ∧, +}`, where `+` is
  exclusive or.
-/
def 𝓑ₗ : Signature := Signature.mk
  (fun | 0 => Constant | 1 => Unary | 2 => Linear | _ => Empty)

instance : Interpretation 𝓑ₗ where
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

instance : Tee   (𝓑ₗ.Formula n) := ⟨.app 0 .true ![]⟩
instance : Void  (𝓑ₗ.Formula n) := ⟨.app 0 .false ![]⟩
instance : Tilde (𝓑ₗ.Formula n) := ⟨fun φ => .app 1 .not ![φ]⟩
instance : Wedge (𝓑ₗ.Formula n) := ⟨fun φ₁ φ₂ => .app 2 .and ![φ₁, φ₂]⟩
instance : Oplus (𝓑ₗ.Formula n) := ⟨fun φ₁ φ₂ => .app 2 .xor ![φ₁, φ₂]⟩

/--
  A function `f` is linear if it is represented by a formula of the form
  `φ(x₁, .., xₙ) = a₀ + (a₁ ∧ x₁) + .. + (aₙ ∧ xₙ)`, for some constants `aᵢ`.
-/
class IsLinear (f : [Bool; n] → Bool) where
  formula : 𝓑ₗ.Formula n
  constants : [Constant; n + 1]
  /-- `formula` has form `φ(x₁, .., xₙ) = a₀ + (a₁ ∧ x₁) + .. + (aₙ ∧ xₙ)`. -/
  hf_form : formula = Σᵇ (fun i : Fin (n + 1) =>
    match i with
    | ⟨0, _⟩ => .app 0 (constants 0) ![]
    | ⟨i+1, h⟩ =>
      (.app 0 (constants (i + 1)) ![]) ⋏
      (.var ⟨i, Nat.succ_lt_succ_iff.mp h⟩)
  )
  hf_repr : formula.represents f

/-- Exercise 1. If a function `f` is linear, its representation is unique. -/
theorem linear_is_unique (l₁ l₂ : IsLinear f) : l₁.constants = l₂.constants := by
  -- likely gonna be by induction on `n`, with `n = 0` being just the constant case.
  sorry

/-- Exercise 2.a -/
theorem 𝓑.unique_formula_reconstruction₁
  (φ: 𝓑.Formula n) (hφ₁ : φ = ~α₁) (hφ₂ : φ = ~α₂) : α₁ = α₂ := sorry

/-- Exercise 2.b -/
theorem 𝓑.unique_formula_reconstruction₂
  (φ: 𝓑.Formula n) (hφ₁ : φ = α₁ ⋏ β₁) (hφ₂ : φ = α₂ ⋏ β₂) :
  α₁ = α₂ ∧ β₁ = β₂ := sorry

/-- Exercise 2.c -/
theorem 𝓑.unique_formula_reconstruction₃
  (φ: 𝓑.Formula n) (hφ₁ : φ = α₁ ⋎ β₁) (hφ₂ : φ = α₂ ⋎ β₂) :
  α₁ = α₂ ∧ β₁ = β₂ := sorry

end Exercises

end Section1
end Chapter1
