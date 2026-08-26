import LifeOfGame.Properties

namespace LifeOfGame

def block : World :=
  {(0, 0), (0, 1), (1, 0), (1, 1)}

def glider : World :=
  {(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)}

def blinker : World :=
  {(-1, 0), (0, 0), (1, 0)}

def singleton : World :=
  {(0, 0)}

def transientBlock : World :=
  block ∪ {(10, 10)}

def twoStepExtinction : World :=
  {(0, 0), (0, 1), (1, 2)}

def transientBlinker : World :=
  blinker ∪ {(10, 10)}

def transientGlider : World :=
  glider ∪ {(10, 10)}

def lightweightSpaceship : World :=
  {(1, 0), (4, 0), (0, 1), (0, 2), (4, 2),
   (0, 3), (1, 3), (2, 3), (3, 3)}

end LifeOfGame
