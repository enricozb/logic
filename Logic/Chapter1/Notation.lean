import Mathlib.Tactic.ScopedNS
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace Notation

/-- Notation for vectors of length `n` with elements of type `α`. -/
scoped notation "[" α ";" n "]" => Fin n → α

/-- The set of `n`-ary boolean functions. -/
scoped notation "𝔹" n => [Bool; n] → Bool

/- These classes define notations for common logical symbols, including their "big" versions. -/

class Tilde (α : Sort _) where tilde : α → α
class Wedge (α : Sort _) where wedge : α → α → α
class Vee   (α : Sort _) where vee   : α → α → α
class Oplus (α : Sort _) where oplus : α → α → α
class Arrow (α : Sort _) where arrow : α → α → α

class BigWedge (α : Sort _) where bigwedge : ∀ {n}, [α; n + 1] → α
class BigVee   (α : Sort _) where bigvee   : ∀ {n}, [α; n + 1] → α
class BigOplus (α : Sort _) where bigoplus : ∀ {n}, [α; n + 1] → α

scoped prefix:75 "~"   => Tilde.tilde
scoped infixl:69 " ⋏ " => Wedge.wedge
scoped infixl:68 " ⋎ " => Vee.vee
scoped infixl:68 " ⊕ " => Oplus.oplus
scoped infixr:60 " ⟶ " => Arrow.arrow
scoped prefix:75 "⋀"   => BigWedge.bigwedge
scoped prefix:75 "⋁"   => BigVee.bigvee
scoped prefix:75 "⨁"   => BigOplus.bigoplus

/-- Folds an operator over a vector. -/
def foldop {a : ℕ} (op : α → α → α) (φs : [α; a + 1]) :=
    match a with
    | 0 => φs 0
    | i + 1 => op (foldop op (Fin.init φs)) (φs (Fin.last (i + 1)))

instance [Wedge α] : BigWedge α := ⟨foldop Wedge.wedge⟩
instance [Vee α]   : BigVee α   := ⟨foldop Vee.vee⟩
instance [Oplus α] : BigOplus α := ⟨foldop Oplus.oplus⟩

instance : Tilde ([Bool; n] → Bool) where tilde f := Bool.not ∘ f
instance : Wedge Bool where wedge := Bool.and
instance : Vee Bool where vee := Bool.or

theorem BigWedge.one [Wedge α] (αs : [α; 1]) : ⋀ αs = αs 0 := by rfl

theorem BigWedge.apply {n : ℕ} [Wedge α] (αs : [α; n + 1 + 1]) :
    ⋀ αs = (⋀ Fin.init αs) ⋏ (αs (Fin.last (n + 1))) := by
  rfl

theorem BigVee.one [Vee α] (αs : [α; 1]) : ⋁ αs = αs 0 := by rfl

theorem BigVee.apply {n : ℕ} [Vee α] (αs : [α; n + 1 + 1]) :
    ⋁ αs = (⋁ Fin.init αs) ⋎ (αs (Fin.last (n + 1))) := by
  rfl

end Notation
