/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackTowerMap

/-!
# Opaque morphisms for pullback towers

A compatible source comparison transports every morphism into the original
object through direct and iterated pullback.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.OverPullbackCoherence
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S T U : C} (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S) (w : h ≫ g = k)

/-- An opaque wrapper for the actual direct-to-iterated pullback morphism. -/
irreducible_def towerMap (X : Over S) :
    (Over.pullback k).obj X ⟶ (Over.pullback h).obj ((Over.pullback g).obj X) :=
  ((towerIso g h k w).app X).hom

/-- Naturality with the tower morphism kept opaque. -/
@[reassoc] theorem towerMap_naturality {X Y : Over S} (f : X ⟶ Y) :
    (Over.pullback k).map f ≫ towerMap g h k w Y =
      towerMap g h k w X ≫ (Over.pullback h).map ((Over.pullback g).map f) := by
  simp only [towerMap_def, Iso.app_hom]
  exact (towerIso g h k w).hom.naturality f

/-- A source square transports every original map through the opaque tower morphism. -/
theorem towerMap_source_square {X Y : Over S} {Z : Over U} {W : Over T} (f : X ⟶ Y)
    (a : Z ⟶ (Over.pullback k).obj X) (b : Z ⟶ (Over.pullback h).obj W)
    (c : W ⟶ (Over.pullback g).obj X)
    (e : a ≫ towerMap g h k w X = b ≫ (Over.pullback h).map c) :
    (a ≫ (Over.pullback k).map f) ≫ towerMap g h k w Y =
      b ≫ (Over.pullback h).map (c ≫ (Over.pullback g).map f) := by
  rw [Category.assoc, towerMap_naturality, ← Category.assoc, e,
    Category.assoc, Functor.map_comp]

end FLT.Mazur.OverPullbackCoherence
