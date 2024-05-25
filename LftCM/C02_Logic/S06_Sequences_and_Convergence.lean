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
  intro ε εpos
  dsimp
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, h⟩
  /- The line `rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, h⟩` can be broken down as follows:

  1. **`cs (ε / |c|) (div_pos εpos acpos)`**:
   - `cs` is the hypothesis that the sequence $$ s $$ converges to $$ a $$.
   - We apply `cs` to $$ \varepsilon / |c| $$ and the proof that $$ \varepsilon / |c| > 0 $$ (which is `div_pos εpos acpos`).

  2. **`rcases ... with ⟨N, h⟩`**:
   - `rcases` is a tactic used for case analysis and destructuring.
   - This extracts the witness $$ N $$ and the proof `h` that for all $$ n \ge N $$, $$ |s n - a| < \varepsilon / |c| $$.

  This step is crucial because it allows us to use the convergence of $$ s $$ to $$ a $$ to show the convergence of $$ c \cdot s $$ to $$ c \cdot a $$.
  -/
  use N
  intro n nge
  calc
  |c * s n - c * a| = |c * (s n - a)| := by congr; ring
  _ = |c| * |s n - a| := by rw [abs_mul]
  _ < |c| * (ε / |c|) := by exact (mul_lt_mul_left acpos).mpr (h n nge)
  _ = ε := by field_simp [mul_comm]

/-
The theorem `convergesTo_mul_const` states that if a sequence \( s \) converges to \( a \), then the sequence obtained by multiplying each term of \( s \) by a constant \( c \) converges to \( c \cdot a \). The proof is structured as follows:

1. **Case \( c = 0 \)**:
   - If \( c = 0 \), then the sequence \( \lambda n, c \cdot s n \) is just the constant sequence \( 0 \), which converges to \( 0 \). This is handled by converting the goal to `convergesTo_const 0` and using the `ring` tactic to simplify.

2. **Case \( c \neq 0 \)**:
   - We first establish that \( |c| > 0 \) using `abs_pos.mpr h`.
   - We then introduce \( \varepsilon \) and assume \( \varepsilon > 0 \).
   - We need to show that \( \lambda n, c \cdot s n \) converges to \( c \cdot a \). For this, we use the fact that \( s \) converges to \( a \).
   - We find \( N \) such that for all \( n \ge N \), \( |s n - a| < \varepsilon / |c| \).
   - We then show that for all \( n \ge N \), \( |c \cdot s n - c \cdot a| < \varepsilon \) by manipulating the inequality and using properties of absolute values and multiplication.

-/

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  calc |s n| = |s n - a + a| := by congr; ring
  _ ≤ |s n - a| + |a| := by exact abs_add_le _ _
  _ < 1 + |a| := by exact add_lt_add_right (h n nge) _
  _ = |a| + 1 := by ring

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nge
  have h₂ : |s n| < B := by
    apply h₀
    exact le_of_max_le_left nge
  have h₃ : |t n - 0| < ε / B := by
    congr
    apply h₁
    exact le_of_max_le_right nge
  -- have h₄ : |s n * t n - 0| = |s n * t n| := by congr; ring
  have h₅ : |s n * t n| = |s n| * |t n| := by rw [abs_mul]
  have h₆ : |t n - 0| = |t n| := by rw [sub_zero]
  have h₇ : |t n| < ε / B := by rwa [← h₆]
  have h₈ : |s n| * |t n| < B * (ε / B) := by gcongr
  simp only [tsub_zero]
  have h₉ : B * (ε / B) = ε := by field_simp [mul_comm]
  linarith

example {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct (ε / B) pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nge
  have h₂ : |s n| < B := by
    apply h₀
    exact le_of_max_le_left nge
  have h₃ : |t n - 0| < ε / B := by
    apply h₁
    exact le_of_max_le_right nge
  calc
    |s n * t n - 0| = |s n * t n| := by rw [sub_zero]
    _ = |s n| * |t n| := by rw [abs_mul]
    _ = |s n| * |t n - 0| := by rw [sub_zero]
    _ < B * (ε / B) := by gcongr
    _ = ε := by field_simp [mul_comm]





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
  have h': |a - b| > 0 := by
    have h₁ : a ≠ b := by
      intro h
      apply abne
      exact h
    have h₂ : a - b ≠ 0 := by
      rw [sub_eq_add_neg]
      have h₃ : a + -b = a - b := by ring
      rw [h₃]
      rwa [sub_ne_zero]
    exact abs_pos.mpr h₂
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    exact le_of_max_le_left (le_refl _)
  have absb : |s N - b| < ε := by
    apply hNb
    exact le_of_max_le_right (le_refl _)
  have h'': |a - b| < |a - b| := by
    calc
    |a - b| = |a - s N + s N - b| := by congr; ring
    _ = |(a - s N) + (s N - b)| := by congr; ring
    _ ≤  |a - s N| + |s N - b| := by exact abs_add_le _ _
    _ = |-(a - s N)| + |s N - b| := by rw [abs_neg]
    _ = |s N - a| + |s N - b| := by simp
    _ < ε + ε := by linarith
    _ = |a - b| := by ring
  linarith

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
