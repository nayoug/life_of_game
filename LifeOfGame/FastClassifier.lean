import LifeOfGame.Classifier
import LifeOfGame.Orbit

namespace LifeOfGame

def extinctStartFast? (fuel : Nat) (states : List World) : Option Nat :=
  findUpTo? fuel (fun start => decide (orbitState states start = ∅))

def stillStartFast? (fuel : Nat) (states : List World) : Option Nat :=
  findUpTo? fuel (fun start => decide (
    start + 1 ≤ fuel ∧ orbitState states start ≠ ∅ ∧
    orbitState states (start + 1) = orbitState states start))

def periodicPeriodFast? (fuel : Nat) (states : List World)
    (start : Nat) : Option Nat :=
  findUpTo? fuel (fun period => decide (
    2 ≤ period ∧ start + period ≤ fuel ∧ start + 1 ≤ fuel ∧
    orbitState states start ≠ ∅ ∧
    orbitState states (start + 1) ≠ orbitState states start ∧
    orbitState states (start + period) = orbitState states start))

def periodicWitnessFast? (fuel : Nat) (states : List World) :
    Option (Nat × Nat) :=
  findSomeUpTo? fuel (periodicPeriodFast? fuel states)

def spaceshipPeriodFast? (fuel : Nat) (states : List World)
    (start : Nat) : Option Nat :=
  findUpTo? fuel (fun period => decide (
    0 < period ∧ start + period ≤ fuel ∧ orbitState states start ≠ ∅ ∧
    orbitState states start ≠ orbitState states (start + period) ∧
    normalize (orbitState states start) =
      normalize (orbitState states (start + period))))

def spaceshipWitnessFast? (fuel : Nat) (states : List World) :
    Option (Nat × Nat) :=
  findSomeUpTo? fuel (spaceshipPeriodFast? fuel states)

def detectFast? (fuel : Nat) (w : World) : Option Detection :=
  let states := orbit fuel w
  match extinctStartFast? fuel states with
  | some start => some (.extinct start)
  | none =>
      match stillStartFast? fuel states with
      | some start => some (.still start)
      | none =>
          match periodicWitnessFast? fuel states with
          | some (start, period) => some (.periodic start period)
          | none =>
              match spaceshipWitnessFast? fuel states with
              | some (start, period) => some (.spaceship start period
                  (displacement (orbitState states start)
                    (orbitState states (start + period))))
              | none => none

theorem extinctStartFast_eq (fuel : Nat) (w : World) :
    extinctStartFast? fuel (orbit fuel w) = extinctStart? fuel w := by
  apply findUpTo_congr
  intro n hn
  rw [orbitState_orbit hn]

theorem stillStartFast_eq (fuel : Nat) (w : World) :
    stillStartFast? fuel (orbit fuel w) = stillStart? fuel w := by
  apply findUpTo_congr
  intro n hn
  by_cases hnext : n + 1 ≤ fuel
  · rw [orbitState_orbit hn, orbitState_orbit hnext]
  · simp [hnext]

theorem periodicPeriodFast_eq (fuel : Nat) (w : World) {start : Nat}
    (hstart : start ≤ fuel) :
    periodicPeriodFast? fuel (orbit fuel w) start =
      periodicPeriod? fuel w start := by
  apply findUpTo_congr
  intro period hperiodFuel
  by_cases hperiod : 2 ≤ period
  · by_cases hbound : start + period ≤ fuel
    · have hnext : start + 1 ≤ fuel := by omega
      rw [orbitState_orbit hstart, orbitState_orbit hnext,
        orbitState_orbit hbound]
    · simp [hbound]
  · simp [hperiod]

theorem periodicWitnessFast_eq (fuel : Nat) (w : World) :
    periodicWitnessFast? fuel (orbit fuel w) = periodicWitness? fuel w := by
  apply findSomeUpTo_congr
  intro start hstart
  exact periodicPeriodFast_eq fuel w hstart

theorem spaceshipPeriodFast_eq (fuel : Nat) (w : World) {start : Nat}
    (hstart : start ≤ fuel) :
    spaceshipPeriodFast? fuel (orbit fuel w) start =
      spaceshipPeriod? fuel w start := by
  apply findUpTo_congr
  intro period hperiodFuel
  by_cases hbound : start + period ≤ fuel
  · rw [orbitState_orbit hstart, orbitState_orbit hbound]
  · simp [hbound]

theorem spaceshipWitnessFast_eq (fuel : Nat) (w : World) :
    spaceshipWitnessFast? fuel (orbit fuel w) = spaceshipWitness? fuel w := by
  apply findSomeUpTo_congr
  intro start hstart
  exact spaceshipPeriodFast_eq fuel w hstart

theorem detectFast_eq_detectSpec (fuel : Nat) (w : World) :
    detectFast? fuel w = detectSpec? fuel w := by
  simp only [detectFast?]
  rw [extinctStartFast_eq, stillStartFast_eq, periodicWitnessFast_eq,
    spaceshipWitnessFast_eq]
  cases hextinct : extinctStart? fuel w with
  | some start => simp [detectSpec?, hextinct]
  | none =>
      cases hstill : stillStart? fuel w with
      | some start => simp [detectSpec?, hextinct, hstill]
      | none =>
          cases hperiodic : periodicWitness? fuel w with
          | some witness => simp [detectSpec?, hextinct, hstill, hperiodic]
          | none =>
              cases hspaceship : spaceshipWitness? fuel w with
              | none =>
                  simp [detectSpec?, hextinct, hstill, hperiodic, hspaceship]
              | some witness =>
                  rcases witness with ⟨start, period⟩
                  have hp := findSomeUpTo_sound hspaceship
                  have hall := of_decide_eq_true (findUpTo_sound hp)
                  have hstart : start ≤ fuel := by omega
                  simp only [hextinct, hstill, hperiodic, hspaceship,
                    detectSpec?]
                  rw [orbitState_orbit hstart, orbitState_orbit hall.2.1]

theorem detectFast_sound {fuel : Nat} {w : World} {d : Detection}
    (h : detectFast? fuel w = some d) : DetectionValid w d := by
  rw [detectFast_eq_detectSpec] at h
  exact detect_sound h

end LifeOfGame
