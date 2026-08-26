import Mathlib.Data.Nat.Basic

namespace LifeOfGame

def findUpTo? (fuel : Nat) (p : Nat → Bool) : Option Nat :=
  match fuel with
  | 0 => if p 0 then some 0 else none
  | n + 1 =>
      match findUpTo? n p with
      | some i => some i
      | none => if p (n + 1) then some (n + 1) else none

def findSomeUpTo? {α : Type} (fuel : Nat) (f : Nat → Option α) :
    Option (Nat × α) :=
  match fuel with
  | 0 => (f 0).map (fun a => (0, a))
  | n + 1 =>
      match findSomeUpTo? n f with
      | some result => some result
      | none => (f (n + 1)).map (fun a => (n + 1, a))

set_option linter.flexible false in
theorem findUpTo_sound {fuel : Nat} {p : Nat → Bool} {n : Nat}
    (h : findUpTo? fuel p = some n) : p n = true := by
  induction fuel with
  | zero =>
      by_cases hp : p 0 = true
      · simp [findUpTo?, hp] at h
        subst n
        exact hp
      · simp [findUpTo?, hp] at h
  | succ fuel ih =>
      cases hprevious : findUpTo? fuel p with
      | some previous =>
          simp [findUpTo?, hprevious] at h
          subst n
          exact ih hprevious
      | none =>
          by_cases hcurrent : p (fuel + 1) = true
          · simp [findUpTo?, hprevious, hcurrent] at h
            subst n
            exact hcurrent
          · simp [findUpTo?, hprevious, hcurrent] at h

set_option linter.flexible false in
theorem findSomeUpTo_sound {α : Type} {fuel : Nat} {f : Nat → Option α}
    {n : Nat} {a : α} (h : findSomeUpTo? fuel f = some (n, a)) :
    f n = some a := by
  induction fuel with
  | zero =>
      cases hvalue : f 0 with
      | none => simp [findSomeUpTo?, hvalue] at h
      | some value =>
          simp [findSomeUpTo?, hvalue] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hvalue
  | succ fuel ih =>
      cases hprevious : findSomeUpTo? fuel f with
      | some previous =>
          simp [findSomeUpTo?, hprevious] at h
          cases h
          exact ih hprevious
      | none =>
          cases hvalue : f (fuel + 1) with
          | none => simp [findSomeUpTo?, hprevious, hvalue] at h
          | some value =>
              simp [findSomeUpTo?, hprevious, hvalue] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hvalue

theorem findUpTo_eq_none {fuel : Nat} {p : Nat → Bool} :
    findUpTo? fuel p = none ↔ ∀ n ≤ fuel, p n = false := by
  induction fuel with
  | zero => simp [findUpTo?]
  | succ fuel ih =>
      constructor
      · intro h n hn
        cases hp : findUpTo? fuel p with
        | some k => simp [findUpTo?, hp] at h
        | none =>
            have hcurrent : p (fuel + 1) = false := by
              simpa [findUpTo?, hp] using h
            by_cases hnf : n ≤ fuel
            · exact ih.mp hp n hnf
            · have : n = fuel + 1 := by omega
              simpa [this] using hcurrent
      · intro h
        have hp : findUpTo? fuel p = none :=
          ih.mpr (fun n hn => h n (by omega))
        have hcurrent := h (fuel + 1) (by omega)
        simp [findUpTo?, hp, hcurrent]

theorem findSomeUpTo_eq_none {α : Type} {fuel : Nat} {f : Nat → Option α} :
    findSomeUpTo? fuel f = none ↔ ∀ n ≤ fuel, f n = none := by
  induction fuel with
  | zero => simp [findSomeUpTo?]
  | succ fuel ih =>
      constructor
      · intro h n hn
        cases hp : findSomeUpTo? fuel f with
        | some result => simp [findSomeUpTo?, hp] at h
        | none =>
            have hcurrent : f (fuel + 1) = none := by
              simpa [findSomeUpTo?, hp] using h
            by_cases hnf : n ≤ fuel
            · exact ih.mp hp n hnf
            · have : n = fuel + 1 := by omega
              simpa [this] using hcurrent
      · intro h
        have hp : findSomeUpTo? fuel f = none :=
          ih.mpr (fun n hn => h n (by omega))
        have hcurrent := h (fuel + 1) (by omega)
        simp [findSomeUpTo?, hp, hcurrent]

set_option linter.flexible false in
theorem findUpTo_le_fuel {fuel : Nat} {p : Nat → Bool} {n : Nat}
    (h : findUpTo? fuel p = some n) : n ≤ fuel := by
  induction fuel with
  | zero =>
      simp [findUpTo?] at h
      omega
  | succ fuel ih =>
      cases hp : findUpTo? fuel p with
      | some k =>
          simp [findUpTo?, hp] at h
          subst n
          exact Nat.le_trans (ih hp) (Nat.le_succ _)
      | none =>
          simp [findUpTo?, hp] at h
          omega

set_option linter.flexible false in
theorem findSomeUpTo_le_fuel {α : Type} {fuel : Nat} {f : Nat → Option α}
    {n : Nat} {a : α} (h : findSomeUpTo? fuel f = some (n, a)) :
    n ≤ fuel := by
  induction fuel with
  | zero =>
      cases hv : f 0 <;> simp [findSomeUpTo?, hv] at h
      omega
  | succ fuel ih =>
      cases hp : findSomeUpTo? fuel f with
      | some result =>
          simp [findSomeUpTo?, hp] at h
          cases h
          exact Nat.le_trans (ih hp) (Nat.le_succ _)
      | none =>
          cases hv : f (fuel + 1) <;> simp [findSomeUpTo?, hp, hv] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Nat.le_refl _

theorem findUpTo_complete {fuel n : Nat} {p : Nat → Bool}
    (hn : n ≤ fuel) (hp : p n = true) :
    ∃ m, findUpTo? fuel p = some m := by
  by_contra hnone
  have hnone' : findUpTo? fuel p = none := by
    cases h : findUpTo? fuel p with
    | none => rfl
    | some m => exact False.elim (hnone ⟨m, h⟩)
  have := findUpTo_eq_none.mp hnone' n hn
  simp [hp] at this

theorem findSomeUpTo_complete {α : Type} {fuel n : Nat} {f : Nat → Option α}
    {a : α} (hn : n ≤ fuel) (hf : f n = some a) :
    ∃ m b, findSomeUpTo? fuel f = some (m, b) := by
  by_contra hnone
  have hnone' : findSomeUpTo? fuel f = none := by
    cases h : findSomeUpTo? fuel f with
    | none => rfl
    | some result =>
        rcases result with ⟨m, b⟩
        exact False.elim (hnone ⟨m, b, h⟩)
  have := findSomeUpTo_eq_none.mp hnone' n hn
  simp [hf] at this

set_option linter.flexible false in
theorem findUpTo_minimal {fuel n : Nat} {p : Nat → Bool}
    (h : findUpTo? fuel p = some n) : ∀ m < n, p m = false := by
  induction fuel with
  | zero =>
      have hn := findUpTo_le_fuel h
      intro m hm
      omega
  | succ fuel ih =>
      cases hp : findUpTo? fuel p with
      | some previous =>
          simp [findUpTo?, hp] at h
          subst n
          exact ih hp
      | none =>
          by_cases hcurrent : p (fuel + 1) = true
          · simp [findUpTo?, hp, hcurrent] at h
            subst n
            intro m hm
            exact findUpTo_eq_none.mp hp m (by omega)
          · simp [findUpTo?, hp, hcurrent] at h

set_option linter.flexible false in
theorem findSomeUpTo_minimal {α : Type} {fuel n : Nat} {f : Nat → Option α}
    {a : α} (h : findSomeUpTo? fuel f = some (n, a)) :
    ∀ m < n, f m = none := by
  induction fuel with
  | zero =>
      have hn := findSomeUpTo_le_fuel h
      intro m hm
      omega
  | succ fuel ih =>
      cases hp : findSomeUpTo? fuel f with
      | some result =>
          simp [findSomeUpTo?, hp] at h
          cases h
          exact ih hp
      | none =>
          cases hv : f (fuel + 1) with
          | none => simp [findSomeUpTo?, hp, hv] at h
          | some value =>
              simp [findSomeUpTo?, hp, hv] at h
              obtain ⟨rfl, rfl⟩ := h
              intro m hm
              exact findSomeUpTo_eq_none.mp hp m (by omega)

theorem findUpTo_congr {fuel : Nat} {p q : Nat → Bool}
    (h : ∀ n ≤ fuel, p n = q n) : findUpTo? fuel p = findUpTo? fuel q := by
  induction fuel with
  | zero => simp [findUpTo?, h 0 (by omega)]
  | succ fuel ih =>
      have hprevious := ih (fun n hn => h n (by omega))
      simp only [findUpTo?]
      rw [hprevious, h (fuel + 1) (by omega)]

theorem findSomeUpTo_congr {α : Type} {fuel : Nat} {f g : Nat → Option α}
    (h : ∀ n ≤ fuel, f n = g n) :
    findSomeUpTo? fuel f = findSomeUpTo? fuel g := by
  induction fuel with
  | zero => simp [findSomeUpTo?, h 0 (by omega)]
  | succ fuel ih =>
      have hprevious := ih (fun n hn => h n (by omega))
      simp only [findSomeUpTo?]
      rw [hprevious, h (fuel + 1) (by omega)]

end LifeOfGame
