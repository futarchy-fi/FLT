/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomDivisorPullback

/-!
# Cartesian comparison of the full cyclic divisor product

The finite product carrying the multiplication equation commutes with every
parameter change as an actual scheme over the original parameter base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)

/-- The whole divisor product is the monoidal pullback of the original product. -/
def cyclicHomDivisorProductPullbackIso :
    cyclicHomDivisorProduct n (k ≫ f) ≅ (Over.pullback k).obj (cyclicHomDivisorProduct n f) :=
  (cyclicHomDivisorPullbackIso n f k ⊗ᵢ cyclicHomDivisorPullbackIso n f k) ≪≫
    Functor.Monoidal.μIso (Over.pullback k) (cyclicHomDivisor n f) (cyclicHomDivisor n f)

/-- The actual map between divisor products induced by a parameter change. -/
def cyclicHomDivisorProductPullbackMap :
    (cyclicHomDivisorProduct n (k ≫ f)).left ⟶ (cyclicHomDivisorProduct n f).left :=
  (cyclicHomDivisorProductPullbackIso n f k).hom.left ≫
    pullback.fst (cyclicHomDivisorProduct n f).hom k

/-- The product comparison lies over the exact original parameter map. -/
@[reassoc] theorem cyclicHomDivisorProductPullbackMap_base :
    cyclicHomDivisorProductPullbackMap n f k ≫ (cyclicHomDivisorProduct n f).hom =
      (cyclicHomDivisorProduct n (k ≫ f)).hom ≫ k := by
  rw [cyclicHomDivisorProductPullbackMap, Category.assoc, pullback.condition,
    ← Category.assoc]
  exact congrArg (· ≫ k) (cyclicHomDivisorProductPullbackIso n f k).hom.w

/-- The entire finite flat product is cartesian over every parameter change. -/
theorem cyclicHomDivisorProductPullbackMap_isPullback :
    IsPullback (cyclicHomDivisorProductPullbackMap n f k)
      (cyclicHomDivisorProduct n (k ≫ f)).hom (cyclicHomDivisorProduct n f).hom k :=
  IsPullback.of_iso_pullback ⟨cyclicHomDivisorProductPullbackMap_base n f k⟩
    ((Over.forget U).mapIso (cyclicHomDivisorProductPullbackIso n f k))
    rfl (cyclicHomDivisorProductPullbackIso n f k).hom.w

end FLT.Mazur.UniversalWeierstrass
