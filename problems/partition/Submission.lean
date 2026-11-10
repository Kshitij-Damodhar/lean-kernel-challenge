import Spec

namespace Submission

/-! ## Implementation -/

/-- Build the next row (parts ≤ k+1) from the old row (parts ≤ k).
`acc` holds the new values so far, most recent first, so `acc[k]` is `new[m-(k+1)]`. -/
def step (k : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc.reverse
  | x :: xs, acc => step k xs ((x + acc.getD k 0) :: acc)

/-- Row `[partAux k 0, ..., partAux k n]`. -/
def rowsAux (n : Nat) : Nat → List Nat
  | 0 => (List.range (n + 1)).map (fun m => if m = 0 then 1 else 0)
  | k + 1 => step k (rowsAux n k) []

/-- TODO 1: Optimized implementation. -/
def impl : Nat → Nat := fun n => (rowsAux n n).getD n 0

/-! ## Helper lemmas about the spec -/

theorem foldl_add (l : List Nat) (a : Nat) :
    l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (a + x), ih (0 + x)]
    omega

def sumTo (F : Nat → Nat) (q : Nat) : Nat :=
  ((List.range q).map F).foldl (· + ·) 0

theorem sumTo_succ (F : Nat → Nat) (q : Nat) :
    sumTo F (q + 1) = F 0 + sumTo (fun j => F (j + 1)) q := by
  unfold sumTo
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldl_cons,
    foldl_add _ (0 + F 0), Nat.zero_add]
  rfl

theorem partAux_succ (k n : Nat) :
    partAux (k + 1) n = sumTo (fun j => partAux k (n - j * (k + 1))) (n / (k + 1) + 1) := by
  unfold sumTo
  first | rfl | rw [partAux]

theorem partAux_rec (k m : Nat) :
    partAux (k + 1) m =
      partAux k m + (if k + 1 ≤ m then partAux (k + 1) (m - (k + 1)) else 0) := by
  by_cases h : k + 1 ≤ m
  · rw [if_pos h]
    have hq : m / (k + 1) = (m - (k + 1)) / (k + 1) + 1 := by
      rw [← Nat.add_div_right _ (by omega : 0 < k + 1), Nat.sub_add_cancel h]
    rw [partAux_succ k m, partAux_succ k (m - (k + 1)), hq,
      sumTo_succ _ ((m - (k + 1)) / (k + 1) + 1)]
    have hF : ∀ j, partAux k (m - (j + 1) * (k + 1)) = partAux k (m - (k + 1) - j * (k + 1)) := by
      intro j
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
      generalize j * (k + 1) = t
      omega
    have hS : sumTo (fun j => partAux k (m - (j + 1) * (k + 1))) ((m - (k + 1)) / (k + 1) + 1)
        = sumTo (fun j => partAux k (m - (k + 1) - j * (k + 1))) ((m - (k + 1)) / (k + 1) + 1) := by
      congr 1
      funext j
      exact hF j
    show partAux k (m - 0 * (k + 1)) +
        sumTo (fun j => partAux k (m - (j + 1) * (k + 1))) _ = _
    rw [hS, Nat.zero_mul, Nat.sub_zero]
  · rw [if_neg h, Nat.add_zero]
    have hq : m / (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [partAux_succ k m, hq, sumTo_succ]
    simp [sumTo]

/-! ## Correctness of `step` -/

theorem step_spec (k : Nat) (f g : Nat → Nat)
    (h : ∀ m, g m = f m + (if k + 1 ≤ m then g (m - (k + 1)) else 0)) :
    ∀ (c m : Nat) (acc : List Nat), acc.length = m →
      (∀ i, i < m → acc.getD i 0 = g (m - 1 - i)) →
      step k ((List.range' m c).map f) acc = acc.reverse ++ (List.range' m c).map g := by
  intro c
  induction c with
  | zero => intro m acc _ _; simp [step]
  | succ c ih =>
    intro m acc hlen hacc
    have hv : f m + acc.getD k 0 = g m := by
      rw [h m]
      by_cases hk : k < m
      · have hk' : k + 1 ≤ m := hk
        have e : m - 1 - k = m - (k + 1) := by omega
        rw [hacc k hk, if_pos hk', e]
      · have hk' : ¬ (k + 1 ≤ m) := by omega
        have h0 : acc.getD k 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
        rw [if_neg hk', h0]
    have hmapf : (List.range' m (c + 1)).map f = f m :: (List.range' (m + 1) c).map f := rfl
    have hmapg : (List.range' m (c + 1)).map g = g m :: (List.range' (m + 1) c).map g := rfl
    rw [hmapf]
    simp only [step]
    rw [hv]
    rw [ih (m + 1) (g m :: acc) (by simp [hlen]) (by
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
        have hj : j < m := by omega
        rw [List.getD_cons_succ, hacc j hj]
        congr 1
        omega)]
    rw [hmapg, List.reverse_cons]
    simp

/-! ## Correctness of the rows -/

theorem rowsAux_eq (n : Nat) : ∀ k, rowsAux n k = (List.range (n + 1)).map (partAux k)
  | 0 => by
    simp only [rowsAux]
    apply List.map_congr_left
    intro m _
    cases m <;> simp [partAux]
  | k + 1 => by
    rw [rowsAux, rowsAux_eq n k]
    have := step_spec k (partAux k) (partAux (k + 1)) (partAux_rec k) (n + 1) 0 []
      rfl (fun i hi => absurd hi (Nat.not_lt_zero _))
    rw [List.range_eq_range']
    rw [this]
    simp

/-- TODO 2: Correctness. -/
theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  unfold impl partitionSpec
  rw [rowsAux_eq]
  first
    | (rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (Nat.lt_succ_self n)]; rfl)
    | simp [List.getD_eq_getElem?_getD]

end Submission
