import LifeOfGame.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

namespace LifeOfGame

open Finset

def neighbors (c : Cell) : Finset Cell :=
  neighborOffsets.image (fun d => addCell c d)

def liveNeighborCount (w : World) (c : Cell) : Nat :=
  ((neighbors c).filter (fun n => n ∈ w)).card

def candidates (w : World) : Finset Cell :=
  w ∪ w.biUnion neighbors

def survivesOrBorn (w : World) (c : Cell) : Bool :=
  liveNeighborCount w c = 3 || (c ∈ w && liveNeighborCount w c = 2)

def next (w : World) : World :=
  (candidates w).filter (fun c => survivesOrBorn w c)

def evolve : Nat → World → World
| 0, w => w
| n + 1, w => evolve n (next w)

@[simp] theorem evolve_zero (w : World) : evolve 0 w = w := rfl

@[simp] theorem evolve_succ (n : Nat) (w : World) :
    evolve (n + 1) w = evolve n (next w) := rfl

theorem evolve_one (w : World) : evolve 1 w = next w := by
  rfl

private theorem count_pos_of_count_eq_three
    (w : World) (c : Cell) (h : liveNeighborCount w c = 3) :
    0 < ((neighbors c).filter (fun n => n ∈ w)).card := by
  simp [liveNeighborCount] at h
  omega

private theorem exists_live_neighbor_of_count_eq_three
    (w : World) (c : Cell) (h : liveNeighborCount w c = 3) :
    ∃ n, n ∈ neighbors c ∧ n ∈ w := by
  have hpos := count_pos_of_count_eq_three w c h
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hn
  exact ⟨n, hn.1, hn.2⟩

theorem mem_biUnion_neighbors_of_live_neighbor
    {w : World} {c n : Cell} (hnc : n ∈ neighbors c) (hnw : n ∈ w) :
    c ∈ w.biUnion neighbors := by
  classical
  rw [neighbors] at hnc
  simp only [Finset.mem_image] at hnc
  obtain ⟨d, hd, hnd⟩ := hnc
  rw [Finset.mem_biUnion]
  refine ⟨n, hnw, ?_⟩
  rw [neighbors, Finset.mem_image]
  refine ⟨negCell d, ?_, ?_⟩
  · simp only [neighborOffsets, Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [negCell]
  · rw [← hnd]
    ext <;> simp [addCell, negCell, add_assoc]

theorem count_eq_three_mem_candidates
    (w : World) (c : Cell) (h : liveNeighborCount w c = 3) :
    c ∈ candidates w := by
  obtain ⟨n, hnc, hnw⟩ := exists_live_neighbor_of_count_eq_three w c h
  rw [candidates, Finset.mem_union]
  exact Or.inr (mem_biUnion_neighbors_of_live_neighbor hnc hnw)

theorem mem_next_iff (w : World) (c : Cell) :
    c ∈ next w ↔
      liveNeighborCount w c = 3 ∨
      (c ∈ w ∧ liveNeighborCount w c = 2) := by
  classical
  constructor
  · intro h
    simp only [next, Finset.mem_filter, survivesOrBorn, Bool.or_eq_true,
      decide_eq_true_eq, Bool.and_eq_true] at h
    exact h.2
  · intro h
    have hcand : c ∈ candidates w := by
      rcases h with h3 | h2
      · exact count_eq_three_mem_candidates w c h3
      · rw [candidates, Finset.mem_union]
        exact Or.inl h2.1
    simp only [next, Finset.mem_filter, survivesOrBorn, Bool.or_eq_true,
      decide_eq_true_eq, Bool.and_eq_true]
    exact ⟨hcand, h⟩

@[simp] theorem next_empty : next (∅ : World) = ∅ := by
  classical
  apply Finset.ext
  intro c
  rw [mem_next_iff]
  simp [liveNeighborCount]

theorem evolve_add (m n : Nat) (w : World) :
    evolve (m + n) w = evolve m (evolve n w) := by
  induction n generalizing w with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ, evolve_succ, evolve_succ, ih]

@[simp] theorem evolve_empty (n : Nat) : evolve n (∅ : World) = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [evolve_succ, ih]

end LifeOfGame
