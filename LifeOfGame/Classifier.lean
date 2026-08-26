import LifeOfGame.Normalization
import LifeOfGame.Search

namespace LifeOfGame

inductive Detection
| extinct (start : Nat)
| still (start : Nat)
| periodic (start period : Nat)
| spaceship (start period : Nat) (delta : Cell)
deriving Repr, DecidableEq

namespace Detection

def status : Detection → Status
| .extinct _ => .extinct
| .still _ => .still
| .periodic _ _ => .periodic
| .spaceship _ _ _ => .spaceship

def start : Detection → Nat
| .extinct n | .still n | .periodic n _ | .spaceship n _ _ => n

end Detection

def extinctStart? (fuel : Nat) (w : World) : Option Nat :=
  findUpTo? fuel (fun start => decide (evolve start w = ∅))

def stillStart? (fuel : Nat) (w : World) : Option Nat :=
  findUpTo? fuel (fun start => decide (
    start + 1 ≤ fuel ∧ evolve start w ≠ ∅ ∧
    evolve (start + 1) w = evolve start w))

def periodicPeriod? (fuel : Nat) (w : World) (start : Nat) : Option Nat :=
  findUpTo? fuel (fun period => decide (
    2 ≤ period ∧ start + period ≤ fuel ∧ start + 1 ≤ fuel ∧
    evolve start w ≠ ∅ ∧ evolve (start + 1) w ≠ evolve start w ∧
    evolve (start + period) w = evolve start w))

def periodicWitness? (fuel : Nat) (w : World) : Option (Nat × Nat) :=
  findSomeUpTo? fuel (periodicPeriod? fuel w)

def spaceshipPeriod? (fuel : Nat) (w : World) (start : Nat) : Option Nat :=
  findUpTo? fuel (fun period => decide (
    0 < period ∧ start + period ≤ fuel ∧ evolve start w ≠ ∅ ∧
    evolve start w ≠ evolve (start + period) w ∧
    normalize (evolve start w) = normalize (evolve (start + period) w)))

def spaceshipWitness? (fuel : Nat) (w : World) : Option (Nat × Nat) :=
  findSomeUpTo? fuel (spaceshipPeriod? fuel w)

theorem extinctStart_sound {fuel : Nat} {w : World} {start : Nat}
    (h : extinctStart? fuel w = some start) : evolve start w = ∅ := by
  exact of_decide_eq_true (findUpTo_sound h)

theorem stillStart_sound {fuel : Nat} {w : World} {start : Nat}
    (h : stillStart? fuel w = some start) :
    evolve start w ≠ ∅ ∧ evolve (start + 1) w = evolve start w := by
  exact (of_decide_eq_true (findUpTo_sound h)).2

theorem periodicPeriod_sound {fuel : Nat} {w : World} {start period : Nat}
    (h : periodicPeriod? fuel w start = some period) :
    IsPeriodicFrom w start period := by
  have hall := of_decide_eq_true (findUpTo_sound h)
  exact ⟨⟨Finset.nonempty_of_ne_empty hall.2.2.2.1,
    by omega, hall.2.2.2.2.2⟩, hall.1, hall.2.2.2.2.1⟩

theorem periodicWitness_sound {fuel : Nat} {w : World} {start period : Nat}
    (h : periodicWitness? fuel w = some (start, period)) :
    IsPeriodicFrom w start period :=
  periodicPeriod_sound (findSomeUpTo_sound h)

theorem spaceshipWitness_sound {fuel : Nat} {w : World} {start period : Nat}
    (h : spaceshipWitness? fuel w = some (start, period)) :
    IsSpaceshipFrom w start period
      (displacement (evolve start w) (evolve (start + period) w)) := by
  have hperiod := findSomeUpTo_sound h
  have hall := of_decide_eq_true (findUpTo_sound hperiod)
  rcases hall with ⟨hpositive, _, hnonempty, hne, hnormalize⟩
  let delta := displacement (evolve start w) (evolve (start + period) w)
  have htranslate : evolve (start + period) w =
      translate delta (evolve start w) := normalize_eq_imp_translate hnormalize
  have hdelta : delta ≠ (0, 0) := by
    intro hz
    rw [hz, translate_zero] at htranslate
    exact hne htranslate.symm
  exact ⟨Finset.nonempty_of_ne_empty hnonempty, hpositive, hdelta, htranslate⟩

theorem extinctStart_complete {fuel start : Nat} {w : World}
    (hbound : start ≤ fuel) (h : evolve start w = ∅) :
    ∃ found, extinctStart? fuel w = some found := by
  exact findUpTo_complete hbound (by simp [h])

theorem stillStart_complete {fuel start : Nat} {w : World}
    (hbound : start + 1 ≤ fuel) (hnonempty : evolve start w ≠ ∅)
    (h : evolve (start + 1) w = evolve start w) :
    ∃ found, stillStart? fuel w = some found := by
  apply findUpTo_complete (n := start) (by omega)
  exact decide_eq_true ⟨hbound, hnonempty, h⟩

theorem periodicPeriod_complete {fuel start period : Nat} {w : World}
    (hperiod : 2 ≤ period) (hbound : start + period ≤ fuel)
    (hnonempty : evolve start w ≠ ∅)
    (hnontrivial : evolve (start + 1) w ≠ evolve start w)
    (hrepeat : evolve (start + period) w = evolve start w) :
    ∃ found, periodicPeriod? fuel w start = some found := by
  apply findUpTo_complete (n := period) (by omega)
  exact decide_eq_true ⟨hperiod, hbound, by omega, hnonempty,
    hnontrivial, hrepeat⟩

theorem periodicWitness_complete {fuel start period : Nat} {w : World}
    (hperiod : 2 ≤ period) (hbound : start + period ≤ fuel)
    (hnonempty : evolve start w ≠ ∅)
    (hnontrivial : evolve (start + 1) w ≠ evolve start w)
    (hrepeat : evolve (start + period) w = evolve start w) :
    ∃ foundStart foundPeriod,
      periodicWitness? fuel w = some (foundStart, foundPeriod) := by
  obtain ⟨found, hfound⟩ :=
    periodicPeriod_complete hperiod hbound hnonempty hnontrivial hrepeat
  exact findSomeUpTo_complete (by omega) hfound

theorem spaceshipPeriod_complete {fuel start period : Nat} {w : World}
    (hperiod : 0 < period) (hbound : start + period ≤ fuel)
    (hnonempty : evolve start w ≠ ∅)
    (hne : evolve start w ≠ evolve (start + period) w)
    (hnormalize : normalize (evolve start w) =
      normalize (evolve (start + period) w)) :
    ∃ found, spaceshipPeriod? fuel w start = some found := by
  apply findUpTo_complete (n := period) (by omega)
  simp [hperiod, hbound, hnonempty, hne, hnormalize]

theorem spaceshipWitness_complete {fuel start period : Nat} {w : World}
    (hperiod : 0 < period) (hbound : start + period ≤ fuel)
    (hnonempty : evolve start w ≠ ∅)
    (hne : evolve start w ≠ evolve (start + period) w)
    (hnormalize : normalize (evolve start w) =
      normalize (evolve (start + period) w)) :
    ∃ foundStart foundPeriod,
      spaceshipWitness? fuel w = some (foundStart, foundPeriod) := by
  obtain ⟨found, hfound⟩ :=
    spaceshipPeriod_complete hperiod hbound hnonempty hne hnormalize
  exact findSomeUpTo_complete (by omega) hfound

theorem extinctStart_minimal {fuel start : Nat} {w : World}
    (h : extinctStart? fuel w = some start) :
    ∀ n < start, evolve n w ≠ ∅ := by
  intro n hn heq
  have hfalse := findUpTo_minimal h n hn
  simp [heq] at hfalse

theorem stillStart_minimal {fuel start : Nat} {w : World}
    (h : stillStart? fuel w = some start) :
    ∀ n < start, ¬ (n + 1 ≤ fuel ∧ evolve n w ≠ ∅ ∧
      evolve (n + 1) w = evolve n w) := by
  intro n hn hcert
  have hfalse := findUpTo_minimal h n hn
  have htrue : decide (n + 1 ≤ fuel ∧ evolve n w ≠ ∅ ∧
      evolve (n + 1) w = evolve n w) = true := decide_eq_true hcert
  rw [htrue] at hfalse
  contradiction

theorem periodicPeriod_minimal {fuel start period : Nat} {w : World}
    (h : periodicPeriod? fuel w start = some period) :
    ∀ p < period, ¬ (2 ≤ p ∧ start + p ≤ fuel ∧ start + 1 ≤ fuel ∧
      evolve start w ≠ ∅ ∧ evolve (start + 1) w ≠ evolve start w ∧
      evolve (start + p) w = evolve start w) := by
  intro p hp hcert
  have hfalse := findUpTo_minimal h p hp
  have htrue : decide (2 ≤ p ∧ start + p ≤ fuel ∧ start + 1 ≤ fuel ∧
      evolve start w ≠ ∅ ∧ evolve (start + 1) w ≠ evolve start w ∧
      evolve (start + p) w = evolve start w) = true := decide_eq_true hcert
  rw [htrue] at hfalse
  contradiction

theorem spaceshipPeriod_minimal {fuel start period : Nat} {w : World}
    (h : spaceshipPeriod? fuel w start = some period) :
    ∀ p < period, ¬ (0 < p ∧ start + p ≤ fuel ∧ evolve start w ≠ ∅ ∧
      evolve start w ≠ evolve (start + p) w ∧
      normalize (evolve start w) = normalize (evolve (start + p) w)) := by
  intro p hp hcert
  have hfalse := findUpTo_minimal h p hp
  have htrue : decide (0 < p ∧ start + p ≤ fuel ∧ evolve start w ≠ ∅ ∧
      evolve start w ≠ evolve (start + p) w ∧
      normalize (evolve start w) = normalize (evolve (start + p) w)) = true :=
    decide_eq_true hcert
  rw [htrue] at hfalse
  contradiction

theorem periodicWitness_start_minimal {fuel start period : Nat} {w : World}
    (h : periodicWitness? fuel w = some (start, period)) :
    ∀ earlier < start, periodicPeriod? fuel w earlier = none :=
  findSomeUpTo_minimal h

theorem spaceshipWitness_start_minimal {fuel start period : Nat} {w : World}
    (h : spaceshipWitness? fuel w = some (start, period)) :
    ∀ earlier < start, spaceshipPeriod? fuel w earlier = none :=
  findSomeUpTo_minimal h

def detectSpec? (fuel : Nat) (w : World) : Option Detection :=
  match extinctStart? fuel w with
  | some start => some (.extinct start)
  | none =>
      match stillStart? fuel w with
      | some start => some (.still start)
      | none =>
          match periodicWitness? fuel w with
          | some (start, period) => some (.periodic start period)
          | none =>
              match spaceshipWitness? fuel w with
              | some (start, period) => some (.spaceship start period
                  (displacement (evolve start w) (evolve (start + period) w)))
              | none => none

abbrev detect? := detectSpec?

def classify? (fuel : Nat) (w : World) : Option Status :=
  (detect? fuel w).map Detection.status

def StatusValid (w : World) : Status → Prop
| .still => EventuallyStill w
| .spaceship => EventuallySpaceship w
| .periodic => EventuallyPeriodic w
| .extinct => EventuallyExtinct w

def DetectionValid (w : World) : Detection → Prop
| .extinct start => evolve start w = ∅
| .still start => (evolve start w).Nonempty ∧
    evolve (start + 1) w = evolve start w
| .periodic start period => IsPeriodicFrom w start period
| .spaceship start period delta => IsSpaceshipFrom w start period delta

set_option linter.flexible false in
theorem detect_sound {fuel : Nat} {w : World} {d : Detection}
    (h : detect? fuel w = some d) : DetectionValid w d := by
  cases hextinct : extinctStart? fuel w with
  | some start =>
      simp [detect?, detectSpec?, hextinct] at h
      subst d
      exact extinctStart_sound hextinct
  | none =>
      cases hstill : stillStart? fuel w with
      | some start =>
          simp [detect?, detectSpec?, hextinct, hstill] at h
          subst d
          have hs := stillStart_sound hstill
          exact ⟨Finset.nonempty_of_ne_empty hs.1, hs.2⟩
      | none =>
          cases hperiodic : periodicWitness? fuel w with
          | some witness =>
              rcases witness with ⟨start, period⟩
              simp [detect?, detectSpec?, hextinct, hstill, hperiodic] at h
              subst d
              exact periodicWitness_sound hperiodic
          | none =>
              cases hspaceship : spaceshipWitness? fuel w with
              | some witness =>
                  rcases witness with ⟨start, period⟩
                  simp [detect?, detectSpec?, hextinct, hstill, hperiodic,
                    hspaceship] at h
                  subst d
                  exact spaceshipWitness_sound hspaceship
              | none =>
                  simp [detect?, detectSpec?, hextinct, hstill, hperiodic,
                    hspaceship] at h

structure VerifiedDetection (w : World) where
  detection : Detection
  valid : DetectionValid w detection

def detectVerified? (fuel : Nat) (w : World) : Option (VerifiedDetection w) :=
  match h : detect? fuel w with
  | none => none
  | some d => some ⟨d, detect_sound h⟩

set_option linter.flexible false in
theorem classify_sound {fuel : Nat} {w : World} {status : Status}
    (h : classify? fuel w = some status) : StatusValid w status := by
  cases hd : detect? fuel w with
  | none => simp [classify?, hd] at h
  | some d =>
      simp [classify?, hd] at h
      subst status
      have hv := detect_sound hd
      cases d with
      | extinct start => exact ⟨start, hv⟩
      | still start => exact ⟨start, hv⟩
      | periodic start period => exact ⟨start, period, hv⟩
      | spaceship start period delta => exact ⟨start, period, delta, hv⟩

theorem classify_still_sound {fuel : Nat} {w : World}
    (h : classify? fuel w = some .still) : EventuallyStill w := classify_sound h

theorem classify_spaceship_sound {fuel : Nat} {w : World}
    (h : classify? fuel w = some .spaceship) : EventuallySpaceship w := classify_sound h

theorem classify_periodic_sound {fuel : Nat} {w : World}
    (h : classify? fuel w = some .periodic) : EventuallyPeriodic w := classify_sound h

theorem classify_extinct_sound {fuel : Nat} {w : World}
    (h : classify? fuel w = some .extinct) : EventuallyExtinct w := classify_sound h

theorem detect_spaceship_complete {fuel : Nat} {w : World}
    (hspaceship : ∃ start period,
      0 < period ∧ start + period ≤ fuel ∧ evolve start w ≠ ∅ ∧
      evolve start w ≠ evolve (start + period) w ∧
      normalize (evolve start w) = normalize (evolve (start + period) w))
    (hnoExtinct : extinctStart? fuel w = none)
    (hnoStill : stillStart? fuel w = none)
    (hnoPeriodic : periodicWitness? fuel w = none) :
    ∃ d, detect? fuel w = some d ∧ d.status = .spaceship := by
  obtain ⟨start, period, hp, hb, hn, hne, hnorm⟩ := hspaceship
  obtain ⟨foundStart, foundPeriod, hfound⟩ :=
    spaceshipWitness_complete hp hb hn hne hnorm
  refine ⟨.spaceship foundStart foundPeriod
    (displacement (evolve foundStart w) (evolve (foundStart + foundPeriod) w)), ?_, rfl⟩
  simp [detect?, detectSpec?, hnoExtinct, hnoStill, hnoPeriodic, hfound]

end LifeOfGame
