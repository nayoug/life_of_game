import LifeOfGame.Translation

namespace LifeOfGame

inductive Status
| still
| spaceship
| periodic
| extinct
deriving Repr, DecidableEq

def IsSpaceshipFrom (w : World) (start period : Nat) (delta : Cell) : Prop :=
  (evolve start w).Nonempty ∧
  0 < period ∧
  delta ≠ (0, 0) ∧
  evolve (start + period) w = translate delta (evolve start w)

def EventuallySpaceship (w : World) : Prop :=
  ∃ start period delta, IsSpaceshipFrom w start period delta

def EventuallyExtinct (w : World) : Prop :=
  ∃ start : Nat, evolve start w = ∅

def EventuallyStill (w : World) : Prop :=
  ∃ start : Nat,
    (evolve start w).Nonempty ∧
    evolve (start + 1) w = evolve start w

def IsRepeatingFrom (w : World) (start period : Nat) : Prop :=
  (evolve start w).Nonempty ∧
  0 < period ∧
  evolve (start + period) w = evolve start w

def EventuallyRepeating (w : World) : Prop :=
  ∃ start period : Nat, IsRepeatingFrom w start period

def IsPeriodicFrom (w : World) (start period : Nat) : Prop :=
  IsRepeatingFrom w start period ∧
  2 ≤ period ∧
  evolve (start + 1) w ≠ evolve start w

def EventuallyPeriodic (w : World) : Prop :=
  ∃ start period : Nat,
    IsPeriodicFrom w start period

@[simp] theorem smulCell_zero (delta : Cell) :
    smulCell 0 delta = (0, 0) := by
  ext <;> simp [smulCell]

theorem smulCell_succ (n : Nat) (delta : Cell) :
    smulCell (n + 1) delta = addCell (smulCell n delta) delta := by
  ext <;> simp [smulCell, addCell, Int.add_mul]

theorem spaceship_repeats_aux
    {state : World} {period : Nat} {delta : Cell}
    (hstep : evolve period state = translate delta state) (k : Nat) :
    evolve (k * period) state = translate (smulCell k delta) state := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.add_comm, evolve_add, ih,
        evolve_translate, hstep, translate_add, smulCell_succ]

theorem spaceship_repeats
    {w : World} {start period : Nat} {delta : Cell}
    (h : IsSpaceshipFrom w start period delta) (k : Nat) :
    evolve (start + k * period) w =
      translate (smulCell k delta) (evolve start w) := by
  have hstep : evolve period (evolve start w) =
      translate delta (evolve start w) := by
    rw [← evolve_add, Nat.add_comm]
    exact h.2.2.2
  rw [Nat.add_comm, evolve_add]
  exact spaceship_repeats_aux hstep k

theorem repeating_repeats_aux
    {state : World} {period : Nat}
    (hstep : evolve period state = state) (k : Nat) :
    evolve (k * period) state = state := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.add_comm, evolve_add, ih, hstep]

theorem repeating_repeats
    {w : World} {start period : Nat}
    (h : IsRepeatingFrom w start period) (k : Nat) :
    evolve (start + k * period) w = evolve start w := by
  have hstep : evolve period (evolve start w) = evolve start w := by
    rw [← evolve_add, Nat.add_comm]
    exact h.2.2
  rw [Nat.add_comm, evolve_add]
  exact repeating_repeats_aux hstep k

theorem still_forever
    {w : World} {start : Nat}
    (hstep : evolve (start + 1) w = evolve start w) (k : Nat) :
    evolve (start + k) w = evolve start w := by
  have hone : evolve 1 (evolve start w) = evolve start w := by
    rw [← evolve_add, Nat.add_comm]
    exact hstep
  rw [Nat.add_comm, evolve_add]
  simpa using (repeating_repeats_aux (period := 1) hone k)

theorem still_of_le
    {w : World} {start n : Nat}
    (hstep : evolve (start + 1) w = evolve start w) (hle : start ≤ n) :
    evolve n w = evolve start w := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact still_forever hstep k

theorem repeating_repeats_next
    {w : World} {start period : Nat}
    (h : IsRepeatingFrom w start period) (k : Nat) :
    evolve (start + k * period + 1) w = evolve (start + 1) w := by
  have hk := congrArg (evolve 1) (repeating_repeats h k)
  rw [← evolve_add 1 (start + k * period) w,
    ← evolve_add 1 start w] at hk
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hk

theorem extinct_forever
    {w : World} {start : Nat} (h : evolve start w = ∅) (k : Nat) :
    evolve (start + k) w = ∅ := by
  rw [Nat.add_comm, evolve_add, h, evolve_empty]

theorem extinct_of_le
    {w : World} {start n : Nat} (h : evolve start w = ∅) (hle : start ≤ n) :
    evolve n w = ∅ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact extinct_forever h k

theorem eventuallyExtinct_not_eventuallyStill {w : World} :
    EventuallyExtinct w → ¬ EventuallyStill w := by
  rintro ⟨extinctStart, hextinct⟩ ⟨stillStart, hnonempty, hstill⟩
  let n := stillStart + extinctStart
  have hempty : evolve n w = ∅ :=
    extinct_of_le hextinct (by simp [n])
  have hsame : evolve n w = evolve stillStart w := by
    exact still_forever hstill extinctStart
  exact hnonempty.ne_empty (by simpa [hsame] using hempty)

theorem eventuallyExtinct_not_eventuallyPeriodic {w : World} :
    EventuallyExtinct w → ¬ EventuallyPeriodic w := by
  rintro ⟨extinctStart, hextinct⟩ ⟨start, period, hperiodic⟩
  let n := start + (extinctStart + 1) * period
  have hle : extinctStart ≤ n := by
    dsimp [n]
    calc
      extinctStart ≤ extinctStart + 1 := Nat.le_succ _
      _ ≤ (extinctStart + 1) * period :=
        Nat.le_mul_of_pos_right _ hperiodic.1.2.1
      _ ≤ start + (extinctStart + 1) * period := by omega
  have hempty : evolve n w = ∅ := extinct_of_le hextinct hle
  have hsame : evolve n w = evolve start w := by
    exact repeating_repeats hperiodic.1 (extinctStart + 1)
  exact hperiodic.1.1.ne_empty (by simpa [hsame] using hempty)

theorem eventuallyExtinct_not_eventuallySpaceship {w : World} :
    EventuallyExtinct w → ¬ EventuallySpaceship w := by
  rintro ⟨extinctStart, hextinct⟩ ⟨start, period, delta, hspaceship⟩
  let n := start + (extinctStart + 1) * period
  have hle : extinctStart ≤ n := by
    dsimp [n]
    calc
      extinctStart ≤ extinctStart + 1 := Nat.le_succ _
      _ ≤ (extinctStart + 1) * period :=
        Nat.le_mul_of_pos_right _ hspaceship.2.1
      _ ≤ start + (extinctStart + 1) * period := by omega
  have hempty : evolve n w = ∅ := extinct_of_le hextinct hle
  have htranslated := spaceship_repeats hspaceship (extinctStart + 1)
  have hcard := congrArg Finset.card htranslated
  rw [hempty, Finset.card_empty, card_translate] at hcard
  exact hspaceship.1.ne_empty (Finset.card_eq_zero.mp hcard.symm)

theorem eventuallyPeriodic_not_eventuallyStill {w : World} :
    EventuallyPeriodic w → ¬ EventuallyStill w := by
  rintro ⟨start, period, hperiodic⟩ ⟨stillStart, _, hstill⟩
  let n := start + (stillStart + 1) * period
  have hle : stillStart ≤ n := by
    dsimp [n]
    calc
      stillStart ≤ stillStart + 1 := Nat.le_succ _
      _ ≤ (stillStart + 1) * period :=
        Nat.le_mul_of_pos_right _ hperiodic.1.2.1
      _ ≤ start + (stillStart + 1) * period := by omega
  have hcycle := repeating_repeats hperiodic.1 (stillStart + 1)
  have hcycleNext := repeating_repeats_next hperiodic.1 (stillStart + 1)
  have hstable := still_of_le hstill hle
  have hstableNext := still_of_le hstill (Nat.le_trans hle (Nat.le_succ _))
  apply hperiodic.2.2
  calc
    evolve (start + 1) w = evolve (n + 1) w := hcycleNext.symm
    _ = evolve stillStart w := hstableNext
    _ = evolve n w := hstable.symm
    _ = evolve start w := hcycle

end LifeOfGame
