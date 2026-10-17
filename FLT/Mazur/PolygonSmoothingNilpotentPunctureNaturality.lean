/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentPunctureEquiv
public import FLT.Mazur.PolygonSmoothingNilpotentShearNaturality
public import FLT.Mazur.PolygonSmoothingRingMapBranch
public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality
public import FLT.Mazur.LaurentUnitSubstitutionNaturality

/-!
# Both puncture automorphisms commute with coefficient change

The full multiplier and its compensating inverse are natural. Consequently
both Laurent automorphisms, including their constructed inverses, commute
with every coefficient restriction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentUnitPoints PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) (hs : f t = s) (e : R) (he : IsNilpotent e)
local notation "F" => ringMap f t s hs

/-- The right-coordinate Laurent restriction is natural without reversing its coordinate. -/
theorem ringMap_rightLaurent :
    ((leftLaurentMap s).comp (branchSwapMap s)).toRingHom.comp F =
      (coeffMap f).comp ((leftLaurentMap t).comp (branchSwapMap t)).toRingHom := by
  change (leftLaurentMap s).toRingHom.comp ((branchSwapMap s).toRingHom.comp F) = _
  rw [ringMap_branchSwap, ← RingHom.comp_assoc, ringMap_leftLaurent, RingHom.comp_assoc]
  rfl

/-- The outgoing full coordinate unit commutes with coefficient restriction. -/
theorem nilpotentShearLeftUnit_map (p : ChartRing t) :
    Units.map (coeffMap f) (nilpotentShearLeftUnit t e he p) =
      nilpotentShearLeftUnit s (f e) (he.map f) (F p) := by
  apply Units.ext
  change coeffMap f (nilpotentShearLeftUnit t e he p : R[T;T⁻¹]) = _
  rw [nilpotentShearLeftUnit_val, nilpotentShearLeftUnit_val,
    map_mul, coeffMap_T_one, map_add, map_one, map_mul, coeffMap_C]
  have h := DFunLike.congr_fun (ringMap_leftLaurent f t s hs) p
  change leftLaurentMap s (F p) = coeffMap f (leftLaurentMap t p) at h
  rw [h]

/-- The opposite unit carries both its scalar drift and full inverse through restriction. -/
theorem nilpotentShearRightUnit_map (c : R) (p : ChartRing t) :
    Units.map (coeffMap f) (nilpotentShearRightUnit t e he c p) =
      nilpotentShearRightUnit s (f e) (he.map f) (f c) (F p) := by
  apply Units.ext
  change coeffMap f (nilpotentShearRightUnit t e he c p : R[T;T⁻¹]) = _
  rw [nilpotentShearRightUnit_val, nilpotentShearRightUnit_val,
    map_mul, coeffMap_C, map_mul, coeffMap_T_one]
  have h := DFunLike.congr_fun (ringMap_rightLaurent f t s hs)
    (↑(nilpotentChartMultiplier t e he p)⁻¹)
  change (leftLaurentMap s).comp (branchSwapMap s)
    (F (↑(nilpotentChartMultiplier t e he p)⁻¹)) =
      coeffMap f ((leftLaurentMap t).comp (branchSwapMap t)
        (↑(nilpotentChartMultiplier t e he p)⁻¹)) at h
  rw [← h]
  simp only [nilpotentChartMultiplier_map_inv, map_add, map_one, map_mul]

/-- The full outgoing automorphism has the original coefficient square. -/
theorem nilpotentShearLeftEquiv_naturality (p : ChartRing t) :
    (coeffMap f).comp (nilpotentShearLeftEquiv t e he p).toAlgHom.toRingHom =
      (nilpotentShearLeftEquiv s (f e) (he.map f) (F p)).toAlgHom.toRingHom.comp
        (coeffMap f) := by
  apply LaurentUnitSubstitutionNaturality.equiv_naturality
  simpa only [nilpotentShearLeftEquiv_toAlgHom, pointUnit_evalUnit] using
    nilpotentShearLeftUnit_map f t s hs e he p

/-- The full opposite automorphism has the same coefficient square. -/
theorem nilpotentShearRightEquiv_naturality (c : R) (p : ChartRing t) :
    (coeffMap f).comp (nilpotentShearRightEquiv t e he c p).toAlgHom.toRingHom =
      (nilpotentShearRightEquiv s (f e) (he.map f) (f c) (F p)).toAlgHom.toRingHom.comp
        (coeffMap f) := by
  apply LaurentUnitSubstitutionNaturality.equiv_naturality
  simpa only [nilpotentShearRightEquiv_toAlgHom, pointUnit_evalUnit] using
    nilpotentShearRightUnit_map f t s hs e he c p

/-- Naturality includes the outgoing inverse on every Laurent function. -/
theorem nilpotentShearLeftEquiv_symm_naturality (p : ChartRing t) :
    (coeffMap f).comp (nilpotentShearLeftEquiv t e he p).symm.toAlgHom.toRingHom =
      (nilpotentShearLeftEquiv s (f e) (he.map f) (F p)).symm.toAlgHom.toRingHom.comp
        (coeffMap f) :=
  LaurentUnitSubstitutionNaturality.symm_naturality f _ _
    (nilpotentShearLeftEquiv_naturality f t s hs e he p)

/-- Naturality also includes the complete compensating inverse on the other puncture. -/
theorem nilpotentShearRightEquiv_symm_naturality (c : R) (p : ChartRing t) :
    (coeffMap f).comp (nilpotentShearRightEquiv t e he c p).symm.toAlgHom.toRingHom =
      (nilpotentShearRightEquiv s (f e) (he.map f) (f c) (F p)).symm.toAlgHom.toRingHom.comp
        (coeffMap f) :=
  LaurentUnitSubstitutionNaturality.symm_naturality f _ _
    (nilpotentShearRightEquiv_naturality f t s hs e he c p)

end FLT.Mazur.PolygonSmoothing
