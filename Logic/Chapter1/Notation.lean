import Mathlib.Tactic.ScopedNS
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace Notation

scoped notation "[" α ";" n "]" => Fin n → α

/- These classes define notations for common logical symbols, including their "big" versions. -/

class Tilde (α : Sort _) where tilde : α → α
class Vee   (α : Sort _) where vee   : α → α → α
class Wedge (α : Sort _) where wedge : α → α → α
class Oplus (α : Sort _) where oplus : α → α → α
class Arrow (α : Sort _) where arrow : α → α → α

class BigVee   (α : Sort _) where bigvee   : ∀ {n}, [α ; n + 1] → α
class BigWedge (α : Sort _) where bigwedge : ∀ {n}, [α ; n + 1] → α
class BigOplus (α : Sort _) where bigoplus : ∀ {n}, [α ; n + 1] → α

scoped prefix:75 "~"   => Tilde.tilde
scoped infixl:69 " ⋏ " => Wedge.wedge
scoped infixl:68 " ⋎ " => Vee.vee
scoped infixl:68 " ⊕ " => Oplus.oplus
scoped prefix:75 "⋀"   => BigWedge.bigwedge
scoped prefix:75 "⋁"   => BigVee.bigvee
scoped infixr:60 " ⟶ " => Arrow.arrow

/-- Folds an operator over a vector. -/
def foldop {a : ℕ} (op : α → α → α) (φs : [α ; a + 1]) :=
    match a with
    | 0 => φs 0
    | i + 1 => op (foldop op (Fin.init φs)) (φs (i + 1))

instance [Oplus α]         : BigOplus α := ⟨foldop Oplus.oplus⟩
instance [Wedge α]         : BigWedge α := ⟨foldop Wedge.wedge⟩
instance [Vee α]           : BigVee α   := ⟨foldop Vee.vee⟩

end Notation
