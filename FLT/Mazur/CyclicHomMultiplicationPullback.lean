/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomDivisorProductPullback
public import FLT.Mazur.CyclicHomDivisorInclusionPullback
public import FLT.Mazur.SmoothCurveMultiplicationPullback

/-!
# Multiplication on the actual cyclic divisor product under pullback

The source and divisor comparisons carry the entire multiplication map,
and therefore its full image ideal, through arbitrary parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)
local instance {V : Scheme} (a : V ⟶ (cyclicHomAuxiliaryScheme n).left) :
    Smooth (cyclicHomSourceCurve n a).curve.hom := SmoothOfRelativeDimension.smooth 1 _
attribute [local instance] smoothCurveCommGrpObj

/-- The entire multiplication map agrees with the monoidal pullback of the original map. -/
theorem cyclicHomDivisorProductMap_pullback :
    cyclicHomDivisorProductMap n (k ≫ f) ≫ (cyclicHomSourcePullbackIso n f k).hom.curve =
      (cyclicHomDivisorProductPullbackIso n f k).hom ≫
        (Over.pullback k).map (cyclicHomDivisorProductMap n f) := by
  dsimp only [cyclicHomDivisorProductMap, ClosedGroupIdeal.productMap]
  rw [Category.assoc, smoothCurvePullbackHom_mul]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  rw [cyclicHomDivisorPullbackIso_inclusion]
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    Functor.LaxMonoidal.μ_natural_assoc]
  rw [← Functor.map_comp]
  rfl

/-- The scheme multiplication square retains the original ambient multiplication. -/
@[reassoc] theorem cyclicHomDivisorProductPullbackMap_multiplication :
    cyclicHomDivisorProductPullbackMap n f k ≫ (cyclicHomDivisorProductMap n f).left =
      (cyclicHomDivisorProductMap n (k ≫ f)).left ≫ cyclicHomSourcePullbackMap n f k := by
  have h := congrArg (fun a ↦ a.left ≫
    pullback.fst (cyclicHomSourceCurve n f).curve.hom k)
    (cyclicHomDivisorProductMap_pullback n f k)
  simpa only [Over.comp_left, Category.assoc, Over.pullback_map_left,
    pullback.lift_fst, cyclicHomDivisorProductPullbackMap, cyclicHomSourcePullbackMap] using h.symm

/-- The full multiplication ideal commutes with arbitrary parameter pullback. -/
theorem cyclicHomMultiplicationIdeal_pullback :
    cyclicHomMultiplicationIdeal n (k ≫ f) =
      (cyclicHomMultiplicationIdeal n f).comap (cyclicHomDivisorProductPullbackMap n f k) := by
  rw [cyclicHomMultiplicationIdeal, cyclicHomMultiplicationIdeal,
    cyclicHomSourceIdeal_pullback, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp,
    cyclicHomDivisorProductPullbackMap_multiplication]

end FLT.Mazur.UniversalWeierstrass
