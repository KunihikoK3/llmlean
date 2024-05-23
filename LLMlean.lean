import LLMlean.LLMstep
import LLMlean.LLMqed
import LeanCopilot
import Mathlib.Data.Real.Basic

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
intro x
show f x + g x ≤ a + b
apply add_le_add
exact hfa x
exact hgb x
