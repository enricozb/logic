import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PNat.Defs
import «Logic».Chapter1.Notation

open Notation

namespace Chapter1
namespace Section1

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

inductive Unary | not
inductive Binary | and | or

/-- The common boolean signature `{¬, ∨, ∧}`. -/
def B : Signature := ⟨fun | 1 => Unary | 2 => Binary | _ => Empty⟩

instance : Tilde (B.Formula V) := ⟨fun α => .app 1 .not ![α]⟩
instance : Wedge (B.Formula V) := ⟨fun α β => .app 2 .and ![α, β]⟩
instance : Vee   (B.Formula V) := ⟨fun α β => .app 2 .or ![α, β]⟩
instance [I : Inhabited V] : Top (B.Formula V) := ⟨.var I.default ⋎ ~.var I.default⟩
instance [I : Inhabited V] : Bot (B.Formula V) := ⟨.var I.default ⋏ ~.var I.default⟩

/-- The common interpretation of `{¬, ∨, ∧}`. -/
instance : Interpretation B where
  fns := fun {n} => match n with
    | 1 => fun
      | .not => fun b => Bool.not (b 0)
    | 2 => fun
      | .and => fun b => Bool.and (b 0) (b 1)
      | .or  => fun b => Bool.or  (b 0) (b 1)
    | 0 | _+3 => fun _ => by contradiction

/-- Boolean formulas with at most `n > 0` variables. -/
abbrev 𝓕 (n : ℕ+) := B.Formula (Fin n)


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

/--
  A formula `α` (with a finite number of variables) represents a boolean function `f : 𝔹 n` if
  they are equal under all models.
-/
def Signature.Formula.represents (α : S.Formula (Fin n)) (f : 𝔹 n) : Prop :=
  ∀ (w : Model (Fin n)), w.value α = f w.valuation

/-- A boolean formula `α` (with a finite number of variables) has an associated boolean function. -/
def Signature.Formula.function (α : S.Formula (Fin n)) : 𝔹 n := (fun b => (Model.mk b).value α)

/-- A boolean formula `α` (with a finite number of variables) represents it's associated boolean function. -/
theorem Signature.Formula.represents_function (α : S.Formula (Fin n)) : α.represents α.function :=
  fun _ => rfl

end Model


namespace Exercises

inductive Constant | true | false
inductive Binary' | and | xor

/--
  The signature of linear functions, `{⊤, ⊥, ¬, ∧, ⊕}`, where `⊕` is exclusive or.
-/
def L : Signature := ⟨fun | 0 => Constant | 1 => Unary | 2 => Binary' | _ => Empty⟩

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

def is_linear (α : L.Formula (Fin n)) (c : [Constant; n + 1]) :=
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
  constants : [Constant; n + 1]
  linear : is_linear α constants

/-- Exercise 1a. The representation of linear functions is unique. -/
theorem linear_is_unique (l₁ : IsLinear f) (l₂ : IsLinear f) : l₁.constants = l₂.constants := by
  sorry

end Exercises

end Section1
end Chapter1
