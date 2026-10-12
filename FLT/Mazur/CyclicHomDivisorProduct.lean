/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomMultiplicationEquation
public import FLT.Mazur.FiniteFlatAffineLocalFree

/-!
# The finite locally free product carrying the multiplication equation

The multiplication obstruction lives on the entire product of the actual
degree-n divisor with itself. Its coordinate algebra is projective over each
affine base open, allowing the coefficient-vanishing construction to apply.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- The actual source orbit divisor over its parameter base. -/
def cyclicHomDivisor : Over T :=
  ClosedGroupIdeal.carrier (cyclicHomSourceCurve n f).curve (cyclicHomSourceIdeal n f)

instance cyclicHomDivisor_isFinite : IsFinite (cyclicHomDivisor n f).hom :=
  (cyclicHomSourceIdeal_degree n f).1

instance cyclicHomDivisor_flat : Flat (cyclicHomDivisor n f).hom :=
  (cyclicHomSourceIdeal_degree n f).2.1

instance cyclicHomDivisor_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (cyclicHomDivisor n f).hom :=
  (cyclicHomSourceIdeal_degree n f).2.2.1

/-- The full product on which multiplication must preserve the divisor. -/
def cyclicHomDivisorProduct : Over T := cyclicHomDivisor n f ⊗ cyclicHomDivisor n f

instance cyclicHomDivisorProduct_isFinite : IsFinite (cyclicHomDivisorProduct n f).hom := by
  change IsFinite (pullback.fst (cyclicHomDivisor n f).hom (cyclicHomDivisor n f).hom ≫
    (cyclicHomDivisor n f).hom)
  infer_instance

instance cyclicHomDivisorProduct_flat : Flat (cyclicHomDivisorProduct n f).hom := by
  change Flat (pullback.fst (cyclicHomDivisor n f).hom (cyclicHomDivisor n f).hom ≫
    (cyclicHomDivisor n f).hom)
  infer_instance

instance cyclicHomDivisorProduct_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (cyclicHomDivisorProduct n f).hom := by
  change LocallyOfFinitePresentation
    (pullback.fst (cyclicHomDivisor n f).hom (cyclicHomDivisor n f).hom ≫
      (cyclicHomDivisor n f).hom)
  infer_instance

local instance : Smooth (cyclicHomSourceCurve n f).curve.hom :=
  SmoothOfRelativeDimension.smooth 1 _
attribute [local instance] smoothCurveCommGrpObj

/-- Ambient multiplication on the actual full divisor product. -/
def cyclicHomDivisorProductMap : cyclicHomDivisorProduct n f ⟶ (cyclicHomSourceCurve n f).curve :=
  ClosedGroupIdeal.productMap _ (cyclicHomSourceIdeal n f)

/-- The image ideal whose vanishing is required on the entire divisor product. -/
def cyclicHomMultiplicationIdeal : (cyclicHomDivisorProduct n f).left.IdealSheafData :=
  (cyclicHomSourceIdeal n f).comap (cyclicHomDivisorProductMap n f).left

/-- The Cartier ideal-map equation is exactly the zero condition on this actual ideal. -/
theorem cyclicHomMultiplicationEquation_iff_ideal :
    cyclicHomMultiplicationEquation n f = 0 ↔ cyclicHomMultiplicationIdeal n f = ⊥ :=
  FCurve.idealModulePullbackι_eq_zero_iff_comap _ _

/-- The actual product algebra is projective over each affine parameter open. -/
theorem cyclicHomDivisorProduct_app_projective (U : T.affineOpens) :
    let _ := ((cyclicHomDivisorProduct n f).hom.app U.1).hom.toAlgebra
    Module.Projective Γ(T, U.1)
      Γ((cyclicHomDivisorProduct n f).left, (cyclicHomDivisorProduct n f).hom ⁻¹ᵁ U.1) :=
  FCurve.finiteFlat_app_projective (cyclicHomDivisorProduct n f).hom U

end FLT.Mazur.UniversalWeierstrass
