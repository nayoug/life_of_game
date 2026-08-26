import LifeOfGame.Properties
import Mathlib.Data.Finset.Max

namespace LifeOfGame

def anchor (w : World) : Cell :=
  if h : w.Nonempty then
    ((w.image Prod.fst).min' (h.image Prod.fst),
      (w.image Prod.snd).min' (h.image Prod.snd))
  else
    (0, 0)

def normalize (w : World) : World :=
  translate (negCell (anchor w)) w

def displacement (a b : World) : Cell :=
  subCell (anchor b) (anchor a)

theorem anchor_translate (delta : Cell) {w : World} (hw : w.Nonempty) :
    anchor (translate delta w) = addCell delta (anchor w) := by
  have ht : (translate delta w).Nonempty := by
    rw [← Finset.card_pos, card_translate, Finset.card_pos]
    exact hw
  rw [anchor, dite_eq_left ht, anchor, dite_eq_left hw]
  apply Prod.ext
  · have htx : ((translate delta w).image Prod.fst).Nonempty := ht.image _
    have hwx : (w.image Prod.fst).Nonempty := hw.image _
    change ((translate delta w).image Prod.fst).min' htx =
      delta.1 + (w.image Prod.fst).min' hwx
    have hi : (translate delta w).image Prod.fst =
        (w.image Prod.fst).image (fun x => delta.1 + x) := by
      simp [translate, Finset.image_image, Function.comp_def, addCell]
    simpa only [hi] using
      (Finset.min'_image (fun _ _ h => Int.add_le_add_left h delta.1)
        (w.image Prod.fst) (hwx.image (fun x => delta.1 + x)))
  · have hty : ((translate delta w).image Prod.snd).Nonempty := ht.image _
    have hwy : (w.image Prod.snd).Nonempty := hw.image _
    change ((translate delta w).image Prod.snd).min' hty =
      delta.2 + (w.image Prod.snd).min' hwy
    have hi : (translate delta w).image Prod.snd =
        (w.image Prod.snd).image (fun x => delta.2 + x) := by
      simp [translate, Finset.image_image, Function.comp_def, addCell]
    simpa only [hi] using
      (Finset.min'_image (fun _ _ h => Int.add_le_add_left h delta.2)
        (w.image Prod.snd) (hwy.image (fun x => delta.2 + x)))

@[simp] theorem addCell_right_neg (a : Cell) :
    addCell a (negCell a) = (0, 0) := by
  rw [addCell_comm, addCell_left_neg]

theorem normalize_eq_imp_translate {a b : World}
    (h : normalize a = normalize b) :
    b = translate (displacement a b) a := by
  have ht := congrArg (translate (anchor b)) h
  simp only [normalize, translate_add] at ht
  rw [addCell_right_neg, translate_zero] at ht
  rw [displacement, subCell_eq_add_neg]
  exact ht.symm

theorem normalize_eq_iff_exists_anchored_translate (a b : World) :
    normalize a = normalize b →
      ∃ delta, b = translate delta a := by
  intro h
  exact ⟨displacement a b, normalize_eq_imp_translate h⟩

theorem normalize_translate (delta : Cell) (w : World) :
    normalize (translate delta w) = normalize w := by
  by_cases hw : w.Nonempty
  · rw [normalize, anchor_translate delta hw, normalize, translate_add]
    congr 1
    ext <;> simp [addCell, negCell]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hw]
    simp [normalize, anchor]

def TranslationEquivalent (a b : World) : Prop :=
  ∃ delta, b = translate delta a

theorem translationEquivalent_refl (w : World) : TranslationEquivalent w w :=
  ⟨(0, 0), (translate_zero w).symm⟩

theorem translationEquivalent_symm {a b : World} :
    TranslationEquivalent a b → TranslationEquivalent b a := by
  rintro ⟨delta, rfl⟩
  refine ⟨negCell delta, ?_⟩
  rw [translate_add, addCell_left_neg, translate_zero]

theorem translationEquivalent_trans {a b c : World} :
    TranslationEquivalent a b → TranslationEquivalent b c →
      TranslationEquivalent a c := by
  rintro ⟨delta₁, rfl⟩ ⟨delta₂, rfl⟩
  exact ⟨addCell delta₂ delta₁, translate_add delta₂ delta₁ a⟩

theorem normalize_eq_iff_exists_translate (a b : World) :
    normalize a = normalize b ↔ TranslationEquivalent a b := by
  constructor
  · exact normalize_eq_iff_exists_anchored_translate a b
  · rintro ⟨delta, rfl⟩
    exact normalize_translate delta a |>.symm

theorem translationEquivalent_iff_normalize_eq (a b : World) :
    TranslationEquivalent a b ↔ normalize a = normalize b :=
  (normalize_eq_iff_exists_translate a b).symm

theorem translate_eq_self_imp_delta_zero
    {w : World} {delta : Cell} (hw : w.Nonempty)
    (h : translate delta w = w) : delta = (0, 0) := by
  have ha := congrArg anchor h
  rw [anchor_translate delta hw] at ha
  apply Prod.ext
  · have hx := congrArg Prod.fst ha
    change delta.1 + (anchor w).1 = (anchor w).1 at hx
    change delta.1 = 0
    omega
  · have hy := congrArg Prod.snd ha
    change delta.2 + (anchor w).2 = (anchor w).2 at hy
    change delta.2 = 0
    omega

end LifeOfGame
