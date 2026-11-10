import Spec

namespace Submission

open ArithmeticFunction

/-- Trial-division Möbius. `fuel` bounds the steps; `d` is the current divisor candidate. -/
def muAux : Nat → Nat → Nat → Int
  | 0, n, _ => if n = 1 then 1 else -1
  | fuel + 1, n, d =>
    if n = 1 then 1
    else if n < d * d then -1                      -- n is prime
    else if n % d = 0 then
      (if (n / d) % d = 0 then 0 else - muAux fuel (n / d) (d + 1))
    else muAux fuel n (d + 1)

def mu (n : Nat) : Int := if n = 0 then 0 else muAux n n 2

/-- Tail-recursive sum of `mu i, mu (i+1), …` (`f` terms). -/
def go : Nat → Nat → Int → Int
  | _, 0, acc => acc
  | i, f + 1, acc => go (i + 1) f (acc + mu i)

def impl (n : Nat) : Int := go 0 (n + 1) 0

/-! ### Möbius lemmas -/

lemma moebius_step {d m : ℕ} (hd : d.Prime) (hdm : ¬ d ∣ m) :
    ArithmeticFunction.moebius (d * m) = - ArithmeticFunction.moebius m := by
  have hc : Nat.Coprime d m := (Nat.Prime.coprime_iff_not_dvd hd).2 hdm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
    ArithmeticFunction.moebius_apply_prime hd]
  ring

lemma moebius_sq {d m : ℕ} (hd : d.Prime) (hdm : d ∣ m) :
    ArithmeticFunction.moebius (d * m) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsq
  obtain ⟨k, rfl⟩ := hdm
  have h := Nat.isUnit_iff.1 (hsq d ⟨k, by ring⟩)
  have := hd.two_le
  omega

lemma prime_of_lt_sq {n d : ℕ} (hn0 : 0 < n) (hn : n ≠ 1)
    (hp : ∀ p, p.Prime → p ∣ n → d ≤ p) (hlt : n < d * d) : n.Prime := by
  by_contra hnp
  have h1 := Nat.minFac_sq_le_self hn0 hnp
  have h2 := hp _ (Nat.minFac_prime hn) (Nat.minFac_dvd n)
  nlinarith

/-! ### Correctness of `muAux` -/

theorem muAux_correct : ∀ (fuel n d : ℕ), 0 < n → 2 ≤ d →
    (∀ p, p.Prime → p ∣ n → d ≤ p) → n ≤ fuel + d →
    muAux fuel n d = ArithmeticFunction.moebius n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n d hn hd hp hle
    by_cases h1 : n = 1
    · subst h1; simp [muAux]
    · have hlt : n < d * d := by nlinarith
      have hpr := prime_of_lt_sq hn h1 hp hlt
      simp [muAux, h1, ArithmeticFunction.moebius_apply_prime hpr]
  | succ f ih =>
    intro n d hn hd hp hle
    by_cases h1 : n = 1
    · subst h1; simp [muAux]
    by_cases h2 : n < d * d
    · have hpr := prime_of_lt_sq hn h1 hp h2
      simp [muAux, h1, h2, ArithmeticFunction.moebius_apply_prime hpr]
    by_cases h3 : n % d = 0
    · -- d is the smallest prime factor of n
      have hdn : d ∣ n := Nat.dvd_of_mod_eq_zero h3
      have hmin : n.minFac = d :=
        le_antisymm (Nat.minFac_le_of_dvd hd hdn)
          (hp _ (Nat.minFac_prime h1) (Nat.minFac_dvd n))
      have hdp : d.Prime := hmin ▸ Nat.minFac_prime h1
      obtain ⟨m, hnm⟩ := hdn
      have hm : n / d = m := by
        rw [hnm]; exact Nat.mul_div_cancel_left _ (by omega)
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; omega
        · exact h
      by_cases h4 : d ∣ m
      · have : (n / d) % d = 0 := by rw [hm]; exact Nat.mod_eq_zero_of_dvd h4
        simp only [muAux, h1, h2, h3, this, if_true, if_false]
        rw [hnm, moebius_sq hdp h4]
      · have h4' : ¬ (n / d) % d = 0 := by
          rw [hm]; exact fun h => h4 (Nat.dvd_of_mod_eq_zero h)
        simp only [muAux, h1, h2, h3, h4', if_true, if_false]
        rw [hm, hnm, moebius_step hdp h4,
          ih m (d + 1) hm0 (by omega) ?_ ?_]
        · intro q hq hqm
          have hqn : q ∣ n := hnm ▸ Dvd.dvd.mul_left hqm d
          have hdq := hp q hq hqn
          have : q ≠ d := fun h => h4 (h ▸ hqm)
          omega
        · have : m ≤ n := by rw [hnm]; nlinarith
          omega
    · simp only [muAux, h1, h2, h3, if_true, if_false]
      apply ih n (d + 1) hn (by omega) _ (by omega)
      intro q hq hqn
      have hdq := hp q hq hqn
      have : q ≠ d := fun h => h3 (Nat.mod_eq_zero_of_dvd (h ▸ hqn))
      omega

theorem mu_eq (n : ℕ) : mu n = ArithmeticFunction.moebius n := by
  by_cases hn : n = 0
  · subst hn; simp [mu]
  · simp only [mu, if_neg hn]
    exact muAux_correct n n 2 (Nat.pos_of_ne_zero hn) le_rfl
      (fun p hp _ => hp.two_le) (by omega)

/-! ### The sum loop -/

theorem go_eq : ∀ (f i : ℕ) (acc : Int),
    go i f acc = acc + ∑ k ∈ Finset.range f, ArithmeticFunction.moebius (i + k) := by
  intro f
  induction f with
  | zero => intro i acc; simp [go]
  | succ f ih =>
    intro i acc
    rw [go, ih, Finset.sum_range_succ' _ f]
    have h : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
    simp only [h, mu_eq, Nat.add_zero]
    ring

/-- Keep the theorem statement unchanged. -/
theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  simp [impl, mertensSpec, go_eq]

end Submission
