import Mathlib.Tactic.SimpRw

@[simp] theorem Bool.not_ite (a b c : Bool) : (!if a then b else c) = if a then !b else !c := by
  by_cases h : a
  · simp_rw [if_pos h]
  · simp_rw [if_neg h]
