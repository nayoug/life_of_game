import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

namespace LifeOfGame

abbrev Cell := Int × Int

abbrev World := Finset Cell

def addCell (a b : Cell) : Cell :=
  (a.1 + b.1, a.2 + b.2)

def negCell (a : Cell) : Cell :=
  (-a.1, -a.2)

def subCell (a b : Cell) : Cell :=
  (a.1 - b.1, a.2 - b.2)

def smulCell (n : Nat) (a : Cell) : Cell :=
  ((n : Int) * a.1, (n : Int) * a.2)

def neighborOffsets : Finset Cell :=
  {(-1, -1), (-1, 0), (-1, 1),
   (0, -1),           (0, 1),
   (1, -1),  (1, 0),  (1, 1)}

@[simp] theorem addCell_zero (a : Cell) : addCell a (0, 0) = a := by
  ext <;> simp [addCell]

@[simp] theorem zero_addCell (a : Cell) : addCell (0, 0) a = a := by
  ext <;> simp [addCell]

@[simp] theorem addCell_assoc (a b c : Cell) :
    addCell (addCell a b) c = addCell a (addCell b c) := by
  ext <;> simp [addCell, add_assoc]

theorem addCell_comm (a b : Cell) : addCell a b = addCell b a := by
  ext <;> simp [addCell, add_comm]

@[simp] theorem addCell_left_neg (a : Cell) : addCell (negCell a) a = (0, 0) := by
  ext <;> simp [addCell, negCell]

@[simp] theorem subCell_eq_add_neg (a b : Cell) :
    subCell a b = addCell a (negCell b) := by
  ext <;> simp [subCell, addCell, negCell, sub_eq_add_neg]

@[simp] theorem addCell_sub_cancel (a b : Cell) :
    addCell (subCell a b) b = a := by
  ext <;> simp [addCell, subCell]

@[simp] theorem subCell_add_cancel (a b : Cell) :
    subCell (addCell a b) b = a := by
  ext <;> simp [addCell, subCell]

end LifeOfGame
