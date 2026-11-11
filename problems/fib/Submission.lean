import Spec

/-!
# Fibonacci by top-down doubling, driven by a bit counter

Mathlib's `Nat.fastFib` and the worked example both recurse on `n` itself:
every level splits `n` into `n / 2` and `n % 2`, recurses on the quotient, and
combines the results on the way back up ("shaving off" the low bit).

Here `n` is never split. A plain counter `i` runs from the number of bits of `n`
down to `0`, and bit `i` is read in place as `(n >>> i) % 2`. The state is the
pair `(F m, F (m+1))` for the current prefix `m = n >>> i`; each step doubles
the index (`m ↦ 2m + bit`) with the usual doubling identities:

  F(2m)   = F(m) * (2*F(m+1) - F(m))        F(2m+1) = F(m+1)^2 + F(m)^2
  F(2m+1) = F(m+1)^2 + F(m)^2               F(2m+2) = F(m+1) * (2*F(m) + F(m+1))

Recursion is structural on the counter, so no well-founded recursion and no
`Nat.binaryRec` unfolding are involved.
-/

namespace Submission

/-- One doubling step. From `(F m, F (m+1))` and a bit `b`, produce
`(F (2m+b), F (2m+b+1))`. -/
def step (b : Nat) (p : Nat × Nat) : Nat × Nat :=
  match p with
  | (x, y) =>
    if b = 0 then
      (x * (2 * y - x), y * y + x * x)
    else
      (y * y + x * x, y * (2 * x + y))

/-- Walk the bits of `n` from position `i - 1` down to `0`.
Invariant: before the call with counter `i`, `p = (F (n >>> i), F (n >>> i + 1))`. -/
def go (n : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | i + 1, p => go n i (step ((n >>> i) % 2) p)

/-- `n.log2 + 1` bits are enough: `n >>> (n.log2 + 1) = 0`. -/
def impl (n : Nat) : Nat := (go n (n.log2 + 1) (0, 1)).1

theorem step_spec (m b : Nat) (hb : b < 2) :
    step b (Nat.fib m, Nat.fib (m + 1)) = (Nat.fib (2 * m + b), Nat.fib (2 * m + b + 1)) := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · have h1 := Nat.fib_two_mul m
    have h2 := Nat.fib_two_mul_add_one m
    simp only [step, if_true, Nat.add_zero, h1, h2, pow_two]
  · have h1 := Nat.fib_two_mul_add_one m
    have h2 := Nat.fib_two_mul_add_two m
    simp only [step, if_neg (by decide : ¬ (1 = 0))]
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from rfl, h1, h2]
    simp only [pow_two]

theorem go_spec (n : Nat) (i : Nat) : ∀ p : Nat × Nat,
    p = (Nat.fib (n >>> i), Nat.fib (n >>> i + 1)) →
    go n i p = (Nat.fib n, Nat.fib (n + 1)) := by
  induction i with
  | zero =>
    intro p h
    simpa [go] using h
  | succ i ih =>
    intro p h
    have hdiv : n >>> (i + 1) = (n >>> i) / 2 := Nat.shiftRight_succ n i
    rw [hdiv] at h
    subst h
    show go n i _ = _
    apply ih
    have hs := step_spec ((n >>> i) / 2) ((n >>> i) % 2) (Nat.mod_lt _ (by decide))
    have he : 2 * ((n >>> i) / 2) + (n >>> i) % 2 = n >>> i := by omega
    rw [he] at hs
    exact hs

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  have h0 : n >>> (n.log2 + 1) = 0 := Nat.shiftRight_eq_zero _ _ Nat.lt_log2_self
  have hg := go_spec n (n.log2 + 1) (0, 1) (by rw [h0]; rfl)
  unfold impl
  rw [hg]

end Submission