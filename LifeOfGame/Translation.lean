import LifeOfGame.Evolution

namespace LifeOfGame

open Finset

def translate (delta : Cell) (w : World) : World :=
  w.image (fun c => addCell delta c)

theorem addCell_left_injective (delta : Cell) :
    Function.Injective (addCell delta) := by
  intro a b h
  ext
  · exact Int.add_left_cancel (congrArg Prod.fst h)
  · exact Int.add_left_cancel (congrArg Prod.snd h)

@[simp] theorem translate_empty (delta : Cell) :
    translate delta (∅ : World) = ∅ := by
  simp [translate]

@[simp] theorem translate_zero (w : World) :
    translate (0, 0) w = w := by
  ext c
  simp [translate, addCell]

theorem translate_add (a b : Cell) (w : World) :
    translate a (translate b w) = translate (addCell a b) w := by
  simp [translate, Finset.image_image, Function.comp_def, addCell_assoc]

@[simp] theorem mem_translate_addCell (delta c : Cell) (w : World) :
    addCell delta c ∈ translate delta w ↔ c ∈ w := by
  constructor
  · intro h
    rw [translate, Finset.mem_image] at h
    obtain ⟨a, ha, hac⟩ := h
    have : a = c := addCell_left_injective delta hac
    simpa [this] using ha
  · intro h
    rw [translate, Finset.mem_image]
    exact ⟨c, h, rfl⟩

@[simp] theorem addCell_subCell_right (a b : Cell) :
    addCell b (subCell a b) = a := by
  ext <;> simp [addCell, subCell]

@[simp] theorem subCell_addCell_left (a b : Cell) :
    subCell (addCell b a) b = a := by
  ext <;> simp [addCell, subCell, add_comm]

theorem mem_translate_iff (delta c : Cell) (w : World) :
    c ∈ translate delta w ↔ subCell c delta ∈ w := by
  rw [← mem_translate_addCell delta (subCell c delta) w]
  rw [addCell_subCell_right]

theorem card_translate (delta : Cell) (w : World) :
    (translate delta w).card = w.card := by
  exact Finset.card_image_of_injective w (addCell_left_injective delta)

theorem neighbors_translate (delta c : Cell) :
    neighbors (addCell delta c) = translate delta (neighbors c) := by
  simp [neighbors, translate, Finset.image_image, Function.comp_def,
    addCell_assoc]

theorem liveNeighborCount_translate (delta : Cell) (w : World) (c : Cell) :
    liveNeighborCount (translate delta w) (addCell delta c) =
      liveNeighborCount w c := by
  unfold liveNeighborCount
  rw [neighbors_translate]
  have hfilter :
      (translate delta (neighbors c)).filter (fun n => n ∈ translate delta w) =
        translate delta ((neighbors c).filter (fun n => n ∈ w)) := by
    ext n
    simp only [Finset.mem_filter, mem_translate_iff]
  rw [hfilter, card_translate]

theorem liveNeighborCount_translate_at (delta : Cell) (w : World) (c : Cell) :
    liveNeighborCount (translate delta w) c =
      liveNeighborCount w (subCell c delta) := by
  have h := liveNeighborCount_translate delta w (subCell c delta)
  rw [addCell_subCell_right] at h
  exact h

theorem next_translate (delta : Cell) (w : World) :
    next (translate delta w) = translate delta (next w) := by
  classical
  ext c
  rw [mem_translate_iff, mem_next_iff, mem_next_iff,
    liveNeighborCount_translate_at, mem_translate_iff]

theorem evolve_translate (n : Nat) (delta : Cell) (w : World) :
    evolve n (translate delta w) = translate delta (evolve n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      rw [evolve_succ, next_translate, ih, evolve_succ]

end LifeOfGame
