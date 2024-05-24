import Mathlib
import LeanCopilot
import Lean
import Paperproof
import LLMlean


namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2 )= fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h


theorem convergesTo_const (a : ℝ) : ConvergesTo (fun ℕ ↦ a) a := by
  intro ε εpos
  -- intro ε εpos introduces the variable ε and the assumption ε > 0 to the context.
  use 0
  -- ConvergesTo contains a *existential* quantifier, so we instantiate it by applying the use tactic.
  intro n
  -- goal contains a *universal* quantifier, so we instantiate it by applying the intro tactic.
  dsimp
  -- dsimp simplifies the goal by expanding the definition of the function.
  simpa using εpos
  -- rw [sub_self, abs_zero]
  -- apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  -- dsimp simplifies the goal by expanding the definition of the function.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  -- destructure the cs hypothesis with ε / 2 and ε2pos to get a suitable Ns and hs.
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have h1 : |s n - a| < ε / 2 := by
    apply hs
    aesop
  have h2 : |t n - b| < ε / 2 := by
    apply ht
    aesop
  have h3 : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
    congr
    ring
  have h4 := add_lt_add h1 h2
  have h5 : |(s n - a) + (t n - b)| ≤ |s n - a| + |t n - b| := by
    exact abs_add_le _ _
  linarith


example {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :ConvergesTo (fun n ↦ s n + t n) (a + b) := by
    intro ε εpos
    dsimp -- this line is not needed but cleans up the goal a bit.
    have ε2pos : 0 < ε / 2 := by linarith
    rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
    rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
    use max Ns Nt
    intro n nge
    have h1 : |s n - a| < ε / 2 := by
      apply hs
      aesop
    have h2 : |t n - b| < ε / 2 := by
      apply ht
      aesop
    calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
      _ ≤ |s n - a| + |t n - b| := by exact abs_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
