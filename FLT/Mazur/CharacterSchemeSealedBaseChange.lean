/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeBaseChangeTower
public import FLT.Mazur.OverPullbackTowerMap

/-!
# Character maps along coefficient towers

Naturality transports the intrinsic source comparison to every character map.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
namespace FLT.Mazur.CharacterSchemeBaseChange
universe u
variable (A B C M : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [AddCommMonoid M]
/-- An opaque copy of the actual intrinsic source isomorphism. -/
irreducible_def sourceIso (R S N : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommMonoid N] : model S N ≅ (Over.pullback (baseMap R S)).obj (model R N) :=
  overIso R S N

/-- Opaque source comparisons obey the actual pullback tower equation. -/
theorem sourceIso_tower :
    (sourceIso A C M).hom ≫
      ((OverPullbackCoherence.towerIso (baseMap A B) (baseMap B C) (baseMap A C)
        (characterTower_baseMap A B C)).app (model A M)).hom =
      (sourceIso B C M).hom ≫ (Over.pullback (baseMap B C)).map (sourceIso A B M).hom := by
  rw [sourceIso_def, sourceIso_def, sourceIso_def]
  exact overIso_tower A B C M

end FLT.Mazur.CharacterSchemeBaseChange
