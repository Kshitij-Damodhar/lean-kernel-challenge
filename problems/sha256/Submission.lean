import Spec

namespace Submission

structure Window where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat
  x8 : Nat
  x9 : Nat
  x10 : Nat
  x11 : Nat
  x12 : Nat
  x13 : Nat
  x14 : Nat
  x15 : Nat

def Window.toList (w : Window) : List Nat :=
  [w.x0, w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7,
   w.x8, w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15]

def Window.nextWord (w : Window) : Nat :=
  add32 (add32 (smallSigma1 w.x14) w.x9)
    (add32 (smallSigma0 w.x1) w.x0)

def Window.push (w : Window) (x : Nat) : Window :=
  ⟨w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7, w.x8,
   w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15, x⟩

def generate : Nat → Window → List Nat
  | 0, _ => []
  | k + 1, w =>
      let x := w.nextWord
      x :: generate k (w.push x)

def initialWindow (d : Digest) : Window :=
  ⟨d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
   0x80000000, 0, 0, 0, 0, 0, 0, 256⟩

def fastSchedule (d : Digest) : List Nat :=
  let w := initialWindow d
  w.toList ++ generate 48 w

def oldStep (d : Digest) : Digest :=
  let f := rounds (K.zip (fastSchedule d)) iv
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d,
   add32 iv.e f.e, add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

theorem drop_last16 (pre : List Nat) (w : Window) :
    (pre ++ w.toList).drop ((pre ++ w.toList).length - 16) = w.toList := by
  simp [Window.toList]

theorem nextWord_eq (w : Window) :
    add32 (add32 (smallSigma1 (w.toList.getD 14 0)) (w.toList.getD 9 0))
      (add32 (smallSigma0 (w.toList.getD 1 0)) (w.toList.getD 0 0)) =
      w.nextWord := by
  rfl

theorem append_push (pre : List Nat) (w : Window) :
    (pre ++ w.toList) ++ [w.nextWord] =
      (pre ++ [w.x0]) ++ (w.push w.nextWord).toList := by
  simp [Window.toList, Window.push]

theorem extend_eq : ∀ k pre w,
    extendW k (pre ++ w.toList) =
      pre ++ w.toList ++ generate k w
  | 0, pre, w => by
      simp [extendW, generate]
  | k + 1, pre, w => by
      rw [extendW, drop_last16, nextWord_eq, append_push]
      rw [extend_eq k (pre ++ [w.x0]) (w.push w.nextWord)]
      simp [generate, Window.toList, Window.push, List.append_assoc]

theorem schedule_correct (d : Digest) :
    fastSchedule d =
      extendW 48 [d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
        0x80000000, 0, 0, 0, 0, 0, 0, 256] := by
  simpa [fastSchedule, initialWindow, Window.toList] using
    (extend_eq 48 [] (initialWindow d)).symm

theorem oldStep_correct (d : Digest) : oldStep d = sha256step d := by
  unfold oldStep sha256step compress
  rw [schedule_correct]

/-- Run rounds while generating schedule words on the fly. -/
def fusedGen : Nat → List Nat → Window → Digest → Digest
  | 0, _, _, s => s
  | _ + 1, [], _, s => s
  | k + 1, kk :: ks, w, s =>
      let x := w.nextWord
      fusedGen k ks (w.push x) (round s kk x)

theorem fused_eq : ∀ (k : Nat) (ks : List Nat) (w : Window) (s : Digest),
    fusedGen k ks w s = rounds (ks.zip (generate k w)) s
  | 0, ks, w, s => by simp [fusedGen, generate, rounds]
  | k + 1, [], w, s => by simp [fusedGen, rounds]
  | k + 1, kk :: ks, w, s => by
      simp [fusedGen, generate, rounds,
        fused_eq k ks (w.push w.nextWord) (round s kk w.nextWord)]

theorem rounds_zip_append : ∀ (ws ks rest : List Nat) (s : Digest),
    rounds (ks.zip (ws ++ rest)) s
      = rounds ((ks.drop ws.length).zip rest) (rounds (ks.zip ws) s)
  | [], ks, rest, s => by simp [rounds]
  | w :: ws, [], rest, s => by simp [rounds]
  | w :: ws, k :: ks, rest, s => by
      simp [rounds, rounds_zip_append ws ks rest (round s k w)]

def fastStep (d : Digest) : Digest :=
  let w := initialWindow d
  let s := rounds (K.zip w.toList) iv
  let f := fusedGen 48 (K.drop 16) w s
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d,
   add32 iv.e f.e, add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

theorem fastStep_eq_old (d : Digest) : fastStep d = oldStep d := by
  have hl : (initialWindow d).toList.length = 16 := rfl
  have h := rounds_zip_append (initialWindow d).toList K
    (generate 48 (initialWindow d)) iv
  rw [hl, ← fused_eq] at h
  simp only [fastStep, oldStep, fastSchedule, h]

theorem fastStep_fun : fastStep = sha256step :=
  funext fun d => (fastStep_eq_old d).trans (oldStep_correct d)

def impl (n : Nat) : Nat :=
  encodeDigest
    (iterDigest fastStep (sha256Steps n) (seedDigest (sha256Seed n)))

theorem impl_correct : ∀ n, impl n = sha256Spec n := fun n =>
  congrArg
    (fun step => encodeDigest
      (iterDigest step (sha256Steps n) (seedDigest (sha256Seed n))))
    fastStep_fun

end Submission
