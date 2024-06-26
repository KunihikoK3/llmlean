-- import LftCM.Common
import Mathlib.Data.Real.Basic
import LeanCopilot

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

/- In words, we would say “for every x, y, and ε, if 0 < ε ≤ 1, the absolute value of x is less than ε, and the absolute value of y is less than ε, then the absolute value of x * y is less than ε.” In Lean, in a sequence of implications there are implicit parentheses grouped to the right. So the expression above means “if 0 < ε then if ε ≤ 1 then if |x| < ε …” As a result, the expression says that all the assumptions together imply the conclusion.

see https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html
-/
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

/-see about twenty lines below for proof of my_lemma-/

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  have h1 : |x| < 1 := by exact xlt.trans_le ele1
  calc
    |x * y| = |x| * |y| := by rw [abs_mul]
    _ ≤ |x| * ε := by gcongr
    _ < 1 * ε := by gcongr
    _ = ε := by rw [one_mul]

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng x
  apply nna

end

section
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

/-In this case, h has type Monotone f, which is defined as ∀ {a b}, a ≤ b → f a ≤ f b. The {a b} part means a and b are implicit arguments. If you wrote just h in the proof, Lean would try to infer a and b, but it doesn't have enough information to do so, so it would insert placeholders (_). By writing @h, you're telling Lean to use h without inferring its implicit arguments, which in this case is exactly what you want, because the goal of the example is ∀ {a b}, a ≤ b → f a ≤ f b, which matches the type of h exactly.
-/
section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb  -- apparently aleb is an implicit argument (hypothesis) of Monotone
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  dsimp
  apply mul_le_mul_of_nonneg_left
  apply mf aleb
  apply nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  dsimp
  apply mf
  apply mg aleb

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  dsimp only
  calc
    f x * g x = -f (-x) * -g (-x) := by rw [of, og]
    _ = f (-x) * g (-x) := by rw [neg_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp only
  calc
    f x * g x = f (-x) * -g (-x) := by rw [ef, og]
    _ = -(f (-x) * g (-x)):= by ring


example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp only
  calc
    f (g x) = f (-g (-x)) := by rw [og]
    _= f (- -g (-x)) := by rw [ef]
    _ = f (g (-x)) := by ring_nf

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro hrs hst x xr
  exact hst (hrs xr)

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x h1
  exact Preorder.le_trans x a b (h x h1) h'


end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  simp only at h'
  simp_all only [mul_eq_mul_left_iff, or_false]

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h'
  exact injf (injg h')

end
