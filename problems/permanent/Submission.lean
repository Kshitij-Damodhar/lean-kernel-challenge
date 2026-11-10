import Spec

namespace Submission

/-! ## Implementation: row-by-row DP over used-column masks -/

/-- Add `c` to the count stored for key `m` (insert if absent). -/
def addTo (m c : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(m, c)]
  | (k, v) :: t =>
      if k = m then (k, v + c) :: t else (k, v) :: addTo m c t

/-- One transition: extend state `p` by column `j` of `row`. -/
def fStep (row : List Nat) (p : Nat × Nat) (acc : List (Nat × Nat)) (j : Nat) :
    List (Nat × Nat) :=
  if row.getD j 0 = 0 || p.1.testBit j then acc
  else addTo (p.1 ||| (1 <<< j)) (p.2 * row.getD j 0) acc

/-- Process one matrix row. -/
def stepRow (w : Nat) (row : List Nat) (S : List (Nat × Nat)) : List (Nat × Nat) :=
  S.foldl (fun acc p => (List.range w).foldl (fStep row p) acc) []

def total (S : List (Nat × Nat)) : Nat := S.foldl (fun a p => a + p.2) 0

def permImpl (M : List (List Nat)) : Nat :=
  total (M.foldl (stepRow M.length) [(0, 1)])

def impl : Nat → Nat := fun n =>
  permImpl (genPermanentMatrix (permanentDimension n) (permanentSeed n))

/-! ## Proof -/

/-- Same step as in `permanentRows`, named so we can reason about it. -/
def gStep (w : Nat) (rows : List (List Nat)) (row : List Nat) (used : Nat)
    (t j : Nat) : Nat :=
  if row.getD j 0 = 0 || used.testBit j then t
  else t + row.getD j 0 * permanentRows w rows (used ||| (1 <<< j))

theorem pr_cons (w : Nat) (row : List Nat) (rows : List (List Nat)) (used : Nat) :
    permanentRows w (row :: rows) used
      = (List.range w).foldl (gStep w rows row used) 0 := by
  first
    | rfl
    | simp [permanentRows, gStep]

theorem pr_nil (w used : Nat) : permanentRows w [] used = 1 := by
  first
    | rfl
    | simp [permanentRows]

theorem fStep_pos {row : List Nat} {p : Nat × Nat} {acc : List (Nat × Nat)} {j : Nat}
    (h : (row.getD j 0 = 0 || p.1.testBit j) = true) : fStep row p acc j = acc := by
  unfold fStep
  exact if_pos h

theorem fStep_neg {row : List Nat} {p : Nat × Nat} {acc : List (Nat × Nat)} {j : Nat}
    (h : ¬ (row.getD j 0 = 0 || p.1.testBit j) = true) :
    fStep row p acc j = addTo (p.1 ||| (1 <<< j)) (p.2 * row.getD j 0) acc := by
  unfold fStep
  exact if_neg h

theorem gStep_pos {w : Nat} {rows : List (List Nat)} {row : List Nat} {used t j : Nat}
    (h : (row.getD j 0 = 0 || used.testBit j) = true) :
    gStep w rows row used t j = t := by
  unfold gStep
  exact if_pos h

theorem gStep_neg {w : Nat} {rows : List (List Nat)} {row : List Nat} {used t j : Nat}
    (h : ¬ (row.getD j 0 = 0 || used.testBit j) = true) :
    gStep w rows row used t j
      = t + row.getD j 0 * permanentRows w rows (used ||| (1 <<< j)) := by
  unfold gStep
  exact if_neg h

/-- Value of a state list against the remaining rows. -/
def val (w : Nat) (rows : List (List Nat)) (S : List (Nat × Nat)) : Nat :=
  (S.map fun p => p.2 * permanentRows w rows p.1).sum

theorem val_cons (w : Nat) (rows : List (List Nat)) (p : Nat × Nat)
    (t : List (Nat × Nat)) :
    val w rows (p :: t) = p.2 * permanentRows w rows p.1 + val w rows t := by
  simp [val]

theorem val_empty (w : Nat) (rows : List (List Nat)) : val w rows [] = 0 := by
  simp [val]

theorem addTo_val (w : Nat) (rows : List (List Nat)) (m c : Nat) :
    ∀ S : List (Nat × Nat),
      val w rows (addTo m c S) = val w rows S + c * permanentRows w rows m := by
  intro S
  induction S with
  | nil => simp [addTo, val]
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases h : k = m
    · subst h
      simp [addTo, val_cons, Nat.add_mul] <;> omega
    · simp [addTo, h, val_cons, ih] <;> omega

theorem perm_inner (w : Nat) (rows : List (List Nat)) (row : List Nat)
    (p : Nat × Nat) :
    ∀ (L : List Nat) (acc : List (Nat × Nat)) (t : Nat),
      val w rows (L.foldl (fStep row p) acc) + p.2 * t
        = val w rows acc + p.2 * (L.foldl (gStep w rows row p.1) t) := by
  intro L
  induction L with
  | nil => intro acc t; simp
  | cons j xs ih =>
    intro acc t
    simp only [List.foldl_cons]
    by_cases hc : (row.getD j 0 = 0 || p.1.testBit j) = true
    · rw [fStep_pos hc, gStep_pos hc]
      exact ih acc t
    · rw [fStep_neg hc, gStep_neg hc]
      have h1 := ih (addTo (p.1 ||| (1 <<< j)) (p.2 * row.getD j 0) acc)
        (t + row.getD j 0 * permanentRows w rows (p.1 ||| (1 <<< j)))
      rw [addTo_val] at h1
      simp only [Nat.mul_add, Nat.mul_assoc] at h1
      omega

theorem perm_outer (w : Nat) (rows : List (List Nat)) (row : List Nat) :
    ∀ (S acc : List (Nat × Nat)),
      val w rows (S.foldl (fun acc p => (List.range w).foldl (fStep row p) acc) acc)
        = val w rows acc + val w (row :: rows) S := by
  intro S
  induction S with
  | nil => intro acc; simp [val]
  | cons p t ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih, val_cons, pr_cons]
    have h := perm_inner w rows row p (List.range w) acc 0
    omega

theorem stepRow_val (w : Nat) (rows : List (List Nat)) (row : List Nat)
    (S : List (Nat × Nat)) :
    val w (row :: rows) S = val w rows (stepRow w row S) := by
  have h := perm_outer w rows row S []
  simp only [val_empty] at h
  unfold stepRow
  omega

theorem val_nil_total (w : Nat) :
    ∀ (S : List (Nat × Nat)) (a : Nat),
      a + val w [] S = S.foldl (fun a p => a + p.2) a := by
  intro S
  induction S with
  | nil => intro a; simp [val]
  | cons p t ih =>
    intro a
    simp only [List.foldl_cons]
    rw [← ih, val_cons, pr_nil]
    omega

theorem foldl_val (w : Nat) :
    ∀ (rows : List (List Nat)) (S : List (Nat × Nat)),
      val w rows S = total (rows.foldl (stepRow w) S) := by
  intro rows
  induction rows with
  | nil =>
    intro S
    have h := val_nil_total w S 0
    simp only [List.foldl_nil, total]
    omega
  | cons row rows ih =>
    intro S
    simp only [List.foldl_cons]
    rw [← ih]
    exact stepRow_val w rows row S

theorem permImpl_correct (M : List (List Nat)) : permImpl M = permanentSpec M := by
  have h := foldl_val M.length M [(0, 1)]
  have h2 : val M.length M [(0, 1)] = permanentRows M.length M 0 := by
    simp [val]
  unfold permImpl permanentSpec
  omega

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  exact permImpl_correct _

end Submission
