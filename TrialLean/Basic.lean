inductive ℕ where
  | zero: ℕ
  | succ: ℕ → ℕ
  deriving Repr
namespace ℕ

axiom zero_ne_succ: ∀n: ℕ, succ n ≠ zero

def one: ℕ := succ zero
def two: ℕ := succ one

def add (a b: ℕ): ℕ :=
  match b with
  | zero    => a
  | succ b' => succ (add a b')
infixl:65 " + " => add

theorem add_zero: ∀a: ℕ, a + zero = a := by
  intro a
  rw [add]

theorem zero_add: ∀a: ℕ, zero + a = a := by
  intro a
  induction a with
  | zero      => rw [add_zero]
  | succ a' h => rw [add, h]

theorem succ_is_add_one: ∀a: ℕ, succ a = a + one := by
  intro a
  rw [one, add, add_zero]

theorem one_plus_one_eq_two: one + one = two := by
  rw [two, one]
  repeat rw [add]

theorem succ_add: ∀a b: ℕ, succ a + b = succ (a + b) := by
  intro a b
  induction b with
  | zero      => rw [add_zero, add_zero]
  | succ b' h => rw [add, h, add]

theorem add_assoc: ∀a b c: ℕ, (a + b) + c = a + (b + c) := by
  intro a b c
  induction a with
  | zero      => rw [zero_add, zero_add]
  | succ a' h => rw [succ_add, succ_add, succ_add, h]

theorem add_commn: ∀a b: ℕ, a + b = b + a := by
  intro a b
  induction b with
  | zero      => rw [add_zero, zero_add]
  | succ b' h => rw [add, succ_add, h]

example: ∀a b c: ℕ, a + b = a + c → b = c := by
  intro a b c p
  induction a with
  | zero => {
    rw [zero_add, zero_add] at p
    exact p
  }
  | succ a' h' => {
    rw [succ_add, succ_add] at p
    injection p with p
    exact h' p
  }

def mul (a b: ℕ): ℕ :=
  match b with
  | zero    => zero
  | succ b' => add (mul a b') a
infixl:75 " ⬝ " => mul

theorem mul_zero: ∀a: ℕ, a ⬝ zero = zero := by
  intro a
  rw [mul]

theorem zero_mul: ∀a: ℕ, zero ⬝ a = zero := by
  intro a
  induction a with
  | zero      => rw [mul_zero]
  | succ a' h => rw [mul, add_zero, h]

theorem mul_one: ∀a: ℕ, a ⬝ one = a := by
  intro a
  rw [one, mul, mul_zero, zero_add]

theorem one_mul: ∀a: ℕ, one ⬝ a = a := by
  intro a
  induction a with
  | zero      => rw [mul_zero]
  | succ a' h => rw [mul, h, one, add, add_zero]

theorem distril: ∀a b c: ℕ, a ⬝ (b + c) = a ⬝ b + a ⬝ c := by
  intro a b c
  induction c with
  | zero      => rw [add_zero, mul_zero, add_zero]
  | succ c' h => rw [add, mul, mul, ←add_assoc, h]

theorem distrir: ∀a b c: ℕ, (a + b) ⬝ c = a ⬝ c + b ⬝ c := by
  intro a b c
  induction c with
  | zero      => rw [mul_zero, mul_zero, mul_zero, add_zero]
  | succ c' h => {
    sorry
  }

theorem mul_assoc: ∀a b c: ℕ, (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c) := by
  intro a b c
  induction c with
  | zero      => rw [mul_zero, mul_zero, mul_zero]
  | succ c' h => rw [mul, mul, distril, h]

theorem mul_commn: ∀a b: ℕ, a ⬝ b = b ⬝ a := by
  intro a b
  induction b with
  | zero      => rw [mul_zero, zero_mul]
  | succ b' h => rw [mul, h, succ_is_add_one, distrir, one_mul]

end ℕ
