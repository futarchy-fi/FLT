/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackTowerComparison

/-!
# Transporting maps through pullback towers

A compatible source comparison transports every morphism into the original
object through direct and iterated pullback.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace FLT.Mazur.OverPullbackCoherence
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S T U : C} (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S) (w : h ≫ g = k)

/-- Naturality transports a compatible source square along any original morphism. -/
theorem tower_map_square {X Y : Over S} {Z : Over U} {W : Over T} (f : X ⟶ Y)
    (a : Z ⟶ (Over.pullback k).obj X) (b : Z ⟶ (Over.pullback h).obj W)
    (c : W ⟶ (Over.pullback g).obj X)
    (e : a ≫ ((towerIso g h k w).app X).hom = b ≫ (Over.pullback h).map c) :
    (a ≫ (Over.pullback k).map f) ≫ ((towerIso g h k w).app Y).hom =
      b ≫ (Over.pullback h).map (c ≫ (Over.pullback g).map f) := by
  simp only [Iso.app_hom] at e ⊢
  rw [Category.assoc, (towerIso g h k w).hom.naturality, ← Category.assoc, e,
    Category.assoc, Functor.map_comp]
  rfl

end FLT.Mazur.OverPullbackCoherence
