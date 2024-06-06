inductive N where
  | zero: N
  | succ: N → N
  deriving Repr
namespace N

axiom zero_ne_succ: ∀n: N, succ n ≠ zero
-- axiom zero_ne_succ (n: N): succ n ≠ zero

axiom succ_inj {a b: N}: succ a = succ b → a = b
-- axiom succ_inj (a b: N): succ a = succ b → a = b
-- axiom succ_inj (a b: N) (h: succ a = succ b): a = b

def one: N := succ zero
def two: N := succ one

def add (a b: N) :=
  match b with
  | zero    => a
  | succ b' => succ (add a b')
infixl:65 " + " => add

theorem zero_add: ∀a: N, zero + a = a := by
  intro a
  induction a
  case zero   => rw [add]
  case succ h => rw [add, h]

theorem one_plus_one_eq_two: one + one = two := by
  rw [two, one]
  repeat rw [add]

theorem succ_add: ∀a b: N, succ a + b = succ (a + b) := by
  intro a b
  induction b
  case zero   => rw [add, add]
  case succ h => rw [add, h, add]

theorem add_assoc: ∀a b c: N, (a + b) + c = a + (b + c) := by
  intro a b c
  induction a
  case zero   => rw [zero_add, zero_add]
  case succ h => rw [succ_add, succ_add, succ_add, h]

theorem add_commn: ∀a b: N, a + b = b + a := by
  intro a b
  induction b
  case zero   => rw [add, zero_add]
  case succ h => rw [add, succ_add, h]

theorem add_cancel: ∀ a b c: N, a + b = a + c → b = c := by
  intro a b c h
  induction a
  case zero    =>
    rw [zero_add, zero_add] at h
    exact h
  case succ h' =>
    rw [succ_add, succ_add] at h
    injection h with h
    apply h' h
end N
