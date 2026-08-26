import LifeOfGame.Evolution

namespace LifeOfGame

def orbit : Nat → World → List World
| 0, w => [w]
| fuel + 1, w => w :: orbit fuel (next w)

@[simp] theorem orbit_length (fuel : Nat) (w : World) :
    (orbit fuel w).length = fuel + 1 := by
  induction fuel generalizing w with
  | zero => rfl
  | succ fuel ih => simp [orbit, ih]

theorem orbit_get? {fuel n : Nat} {w : World} (h : n ≤ fuel) :
    (orbit fuel w)[n]? = some (evolve n w) := by
  induction fuel generalizing n w with
  | zero =>
      have : n = 0 := by omega
      subst n
      rfl
  | succ fuel ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [orbit, List.getElem?_cons_succ, evolve_succ]
          exact ih (by omega)

def orbitState (states : List World) (n : Nat) : World :=
  (states[n]?).getD ∅

theorem orbitState_orbit {fuel n : Nat} {w : World} (h : n ≤ fuel) :
    orbitState (orbit fuel w) n = evolve n w := by
  rw [orbitState, orbit_get? h]
  rfl

end LifeOfGame
