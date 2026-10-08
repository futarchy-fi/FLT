/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryDomainLift
public import FLT.Mazur.WeierstrassSpecSectionMorphism

/-!
# Ordinary chart lifts from arbitrary common schemes

The affine-output locus of a reciprocal chart factors through its corresponding
ordinary chart. The factorization preserves the actual input-pair morphism,
not just its points, and requires no reducedness or affineness of the source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (W : WeierstrassCurve R)

/-- Recover an ordinary chart morphism from an invertible denominator on global sections. -/
def ordinarySchemeLift (b : Bool) (f : X ⟶ Spec (.of (AffineProduct W)))
    (hf : IsUnit (specSectionHom f
      (if b then tangentDenominator W else secantDenominator W))) :
    X ⟶ Spec (additionChartRing W (ordinaryIndex b)) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W)))
  let _ := specSectionAlgebra s
  exact specSectionMorphism
    (ordinaryDomainLift W b (specSectionAlgHom s f rfl) hf).toRingHom

/-- The recovered ordinary morphism retains the same affine input pair. -/
theorem ordinarySchemeLift_inputs (b : Bool) (f : X ⟶ Spec (.of (AffineProduct W)))
    (hf : IsUnit (specSectionHom f
      (if b then tangentDenominator W else secantDenominator W))) :
    ordinarySchemeLift W b f hf ≫ additionChartInclusion W (ordinaryIndex b) = f := by
  let s := f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W)))
  let _ := specSectionAlgebra s
  apply specSectionHom_injective
  rw [additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    specSectionHom_comp]
  change (specSectionHom (specSectionMorphism
    (ordinaryDomainLift W b (specSectionAlgHom s f rfl) hf).toRingHom)).comp _ = _
  rw [specSectionHom_morphism]
  exact congrArg AlgHom.toRingHom (ordinaryDomainLift_restriction W b
    (specSectionAlgHom s f rfl) hf)

/-- Affine reciprocal output provides the ordinary denominator on the same scheme. -/
theorem reciprocalScheme_ordinary_unit (b : Bool)
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (hz : IsUnit (specSectionHom f (reciprocalChartAddition W b (coord W 1 2)))) :
    IsUnit (specSectionHom (f ≫ additionChartInclusion W (reciprocalIndex b))
      (if b then tangentDenominator W else secantDenominator W)) := by
  let s := f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (additionChartRing W (reciprocalIndex b))))
  let _ := specSectionAlgebra s
  rw [additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    specSectionHom_comp]
  exact reciprocalSpecialization_ordinary_unit W b
    (specSectionAlgHom (A := additionChartRing W (reciprocalIndex b)) s f rfl) hz

/-- A reciprocal chart with affine output factors through the matching ordinary chart. -/
def reciprocalAffineOrdinaryScheme (b : Bool)
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (hz : IsUnit (specSectionHom f (reciprocalChartAddition W b (coord W 1 2)))) :
    X ⟶ Spec (additionChartRing W (ordinaryIndex b)) :=
  ordinarySchemeLift W b (f ≫ additionChartInclusion W (reciprocalIndex b))
    (reciprocalScheme_ordinary_unit W b f hz)

/-- Replacing the reciprocal domain preserves the actual pair of inputs. -/
theorem reciprocalAffineOrdinaryScheme_inputs (b : Bool)
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (hz : IsUnit (specSectionHom f (reciprocalChartAddition W b (coord W 1 2)))) :
    reciprocalAffineOrdinaryScheme W b f hz ≫
        additionChartInclusion W (ordinaryIndex b) =
      f ≫ additionChartInclusion W (reciprocalIndex b) :=
  ordinarySchemeLift_inputs W b _ _

end FLT.Mazur.WeierstrassIntegralChart
