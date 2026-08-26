import LifeOfGame.Patterns
import LifeOfGame.FastClassifier

set_option linter.style.nativeDecide false

namespace LifeOfGame

example : next singleton = ∅ := by native_decide
example : next block = block := by native_decide

theorem block_eventuallyStill : EventuallyStill block := by
  refine ⟨0, ?_, ?_⟩ <;> native_decide

theorem glider_eventuallySpaceship : EventuallySpaceship glider := by
  refine ⟨0, 4, (1, 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem blinker_eventuallyPeriodic : EventuallyPeriodic blinker := by
  refine ⟨0, 2, ?_⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> native_decide

theorem singleton_eventuallyExtinct : EventuallyExtinct singleton := by
  exact ⟨1, by native_decide⟩

theorem singleton_not_eventuallySpaceship : ¬ EventuallySpaceship singleton :=
  eventuallyExtinct_not_eventuallySpaceship singleton_eventuallyExtinct

theorem transientBlock_eventuallyStill : EventuallyStill transientBlock := by
  exact ⟨1, by native_decide⟩

theorem twoStepExtinction_eventuallyExtinct :
    EventuallyExtinct twoStepExtinction := by
  exact ⟨2, by native_decide⟩

theorem transientBlinker_eventuallyPeriodic :
    EventuallyPeriodic transientBlinker := by
  refine ⟨1, 2, ?_⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> native_decide

theorem transientGlider_eventuallySpaceship :
    EventuallySpaceship transientGlider := by
  refine ⟨1, 4, (1, 1), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem lightweightSpaceship_eventuallySpaceship :
    EventuallySpaceship lightweightSpaceship := by
  refine ⟨0, 4, (-2, 0), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

example : classify? 4 block = some .still := by native_decide
example : classify? 4 glider = some .spaceship := by native_decide
example : classify? 4 blinker = some .periodic := by native_decide
example : classify? 4 singleton = some .extinct := by native_decide
example : classify? 0 block = none := by native_decide
example : classify? 2 transientBlock = some .still := by native_decide

example : classify? 1 twoStepExtinction = none := by native_decide
example : classify? 2 twoStepExtinction = some .extinct := by native_decide
example : classify? 2 transientBlinker = none := by native_decide
example : classify? 3 transientBlinker = some .periodic := by native_decide
example : classify? 4 transientGlider = none := by native_decide
example : classify? 5 transientGlider = some .spaceship := by native_decide
example : classify? 4 lightweightSpaceship = some .spaceship := by native_decide

example : detectFast? 5 transientGlider = detect? 5 transientGlider := by
  exact detectFast_eq_detectSpec _ _

example : detectFast? 4 lightweightSpaceship =
    some (.spaceship 0 4 (-2, 0)) := by native_decide

#eval detect? 2 twoStepExtinction
#eval detect? 3 transientBlinker
#eval detect? 5 transientGlider
#eval detect? 4 lightweightSpaceship
#eval detectFast? 5 transientGlider

end LifeOfGame
