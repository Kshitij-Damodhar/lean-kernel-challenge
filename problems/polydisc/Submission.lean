import Spec

namespace Submission

/-- One division per coefficient instead of `%` followed by `/`. -/
def exactDivideFast (d : Int) : List Int → Option (List Int)
  | [] => some []
  | c :: cs =>
      if d == 0 then none
      else
        let q := c / d
        if q * d != c then none
        else
          match exactDivideFast d cs with
          | none => none
          | some rest => some (q :: rest)

theorem div_key (c d : Int) : (c / d * d = c) ↔ (c % d = 0) := by
  constructor
  · intro h
    have e := Int.emod_def c d
    rw [Int.mul_comm d (c / d), h] at e
    simpa using e
  · intro h
    exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)

theorem exactDivideFast_eq (d : Int) :
    ∀ l, exactDivideFast d l = exactDividePolynomial d l
  | [] => by simp [exactDivideFast, exactDividePolynomial]
  | c :: cs => by
      have ih := exactDivideFast_eq d cs
      by_cases h0 : d = 0
      · subst h0
        simp [exactDivideFast, exactDividePolynomial]
      · by_cases hc : c % d = 0
        · have hq : c / d * d = c := (div_key c d).mpr hc
          simp [h0, hc, hq, ih, exactDivideFast, exactDividePolynomial]
        · have hq : ¬ (c / d * d = c) := fun h => hc ((div_key c d).mp h)
          simp [h0, hc, hq, ih, exactDivideFast, exactDividePolynomial]

def normalResultantGoF :
    Nat → Bool → List Int → List Int → Option Int
  | 0, _, _, _ => none
  | fuel + 1, initial, f, g =>
      match pseudoRemainder f g with
      | none => none
      | some raw =>
          let divided :=
            if initial then some raw
            else exactDivideFast ((f.headD 0) ^ 2) raw
          match divided with
          | none => none
          | some coefficients =>
              match trimLeading coefficients with
              | [] => some 0
              | remainder =>
                  if remainder.length + 1 == g.length then
                    match remainder with
                    | [constant] => some constant
                    | _ => normalResultantGoF fuel false g remainder
                  else
                    none

theorem normalResultantGoF_eq :
    ∀ (fuel : Nat) (initial : Bool) (f g : List Int),
      normalResultantGoF fuel initial f g = normalResultantGo fuel initial f g
  | 0, _, _, _ => by simp [normalResultantGoF, normalResultantGo]
  | fuel + 1, initial, f, g => by
      have ih := normalResultantGoF_eq fuel
      simp [normalResultantGoF, normalResultantGo, exactDivideFast_eq, ih]

def normalResultantF (f g : List Int) : Option Int :=
  let f := trimLeading f
  let g := trimLeading g
  if f.length == g.length + 1 && !g.isEmpty then
    normalResultantGoF (g.length + 1) true f g
  else
    none

theorem normalResultantF_eq (f g : List Int) :
    normalResultantF f g = normalResultant f g := by
  simp [normalResultantF, normalResultant, normalResultantGoF_eq]

def resultantFromPolyF (p : List Int) : Int :=
  let derivative := derivHL p
  match normalResultantF p derivative with
  | some resultant => resultant
  | none => bareissDet (monicReducedSylvester p derivative)

theorem resultantFromPolyF_eq (p : List Int) :
    resultantFromPolyF p = resultantFromPoly p := by
  simp [resultantFromPolyF, resultantFromPoly, normalResultantF_eq]

def discriminantFromPolyF (p : List Int) : Int :=
  let degree := p.length - 1
  let sign : Int :=
    if degree * (degree - 1) / 2 % 2 = 0 then 1 else -1
  sign * resultantFromPolyF p

def impl : Nat → Int := fun n => discriminantFromPolyF (polyOf n)

theorem impl_correct : ∀ n, impl n = discSpec n := by
  intro n
  show discriminantFromPolyF (polyOf n) = discriminantFromPoly (polyOf n)
  simp only [discriminantFromPolyF, discriminantFromPoly, resultantFromPolyF_eq]

end Submission
