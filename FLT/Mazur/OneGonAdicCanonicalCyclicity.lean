/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCanonicalOrbit
public import FLT.Mazur.RootsOfUnitySubgroupCyclicity
public import FLT.Mazur.GeneralizedCurveCartierDescent

/-!
# Cartier cyclicity on the genuine complete-base degeneration

The actual canonical subgroup is cyclic by its cyclotomic fppf cover, with
its original embedding and group law retained. Cartier descent then removes
the Noetherian restriction from the full ideal and its ampleness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonAdicCharacterTower

open ArithmeticOneGonGeneralizedCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The full generator orbit is the entire original canonical subgroup ideal. -/
theorem canonicalGenerator_ideal_eq (φ : IntegralCyclotomicCoordinates.Coordinate n →+* R) :
    (canonicalFiniteSubgroup I t ht n).ideal =
      ∏ k : Fin n, ((canonicalGenerator I t ht n φ ^ k.val) ≫
        (canonicalFiniteSubgroup I t ht n).curveMap).left.ker :=
  (FCurve.idealSheaf_eq_of_le_of_finiteLocallyFreeDegree
    (curve t (complementaryFactor_isUnit I t ht)).curve.hom _ _
    (canonicalGenerator_orbit_le I t ht n φ) n
    (canonicalGenerator_orbit_degree I t ht n φ)
    (canonicalFiniteSubgroup I t ht n).ideal_degree).symm

/-- The specified root is a Cartier generator without Noetherian or invertibility hypotheses. -/
theorem canonicalGenerator_isCartierGenerator
    (φ : IntegralCyclotomicCoordinates.Coordinate n →+* R) :
    (canonicalFiniteSubgroup I t ht n).IsCartierGenerator (canonicalGenerator I t ht n φ) := by
  let _ : SmoothOfRelativeDimension 1 (curve t (complementaryFactor_isUnit I t ht)).group.hom :=
    WeierstrassIntegralChart.integralSmoothStructure_relativeDimension (OneGonSmoothing.equation t)
  exact (canonicalFiniteSubgroup I t ht n).isCartierGenerator_of_intrinsic_orbit _
    (canonicalGenerator_pow I t ht n φ) (RootsOfUnityIntrinsicOrbit.orbit_product_zero n φ)

/-- The actual rank-n subgroup is cyclic on the original nonconstant complete-base family. -/
theorem canonicalFiniteSubgroup_isCyclic : (canonicalFiniteSubgroup I t ht n).IsCyclic := by
  let _ : SmoothOfRelativeDimension 1 (curve t (complementaryFactor_isUnit I t ht)).group.hom :=
    WeierstrassIntegralChart.integralSmoothStructure_relativeDimension (OneGonSmoothing.equation t)
  let _ : IsMonHom (Iso.refl (RootsOfUnityScheme.model R n)).hom :=
    inferInstanceAs (IsMonHom (𝟙 (RootsOfUnityScheme.model R n)))
  exact (canonicalFiniteSubgroup I t ht n).isCyclic_of_rootsIso (Iso.refl _)

/-- The full original ideal is relative Cartier over every complete coefficient ring. -/
theorem canonicalFiniteSubgroup_relativeCartier_unrestricted :
    FCurve.RelativeEffectiveCartier (curve t (complementaryFactor_isUnit I t ht)).curve.hom
      (canonicalFiniteSubgroup I t ht n).ideal :=
  (canonicalFiniteSubgroup_isCyclic I t ht n).relativeEffectiveCartier _

/-- The canonical subgroup is ample without requiring Noetherian coefficients. -/
theorem canonicalFiniteSubgroup_isAmple_unrestricted :
    (canonicalFiniteSubgroup I t ht n).IsAmple :=
  ArithmeticOneGonSubgroupAmple.isAmple t (complementaryFactor_isUnit I t ht) _
    (NeZero.pos n) (canonicalFiniteSubgroup_relativeCartier_unrestricted I t ht n).1

/-- The genuine integral power-series degeneration has the constructed cyclic subgroup. -/
theorem integralPowerSeriesFiniteSubgroup_isCyclic :
    (integralPowerSeriesFiniteSubgroup n).IsCyclic :=
  canonicalFiniteSubgroup_isCyclic _ _ _ n

end FLT.Mazur.OneGonAdicCharacterTower
