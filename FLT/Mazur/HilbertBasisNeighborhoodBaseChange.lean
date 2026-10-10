/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisNeighborhoodCompatibility
public import FLT.Mazur.HilbertPrincipalBaseChangeScalars

/-!
# Base change of actual principal basis neighborhoods

The image of a principal basis neighborhood is again a basis neighborhood.
Its parameter is the composite with the actual map of principal localizations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable (R : Type*) [CommRing R] (I : Type*) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Extending an ideal in two steps equals extension along the composite scalar map. -/
theorem polynomialIdeal_map_tower (U : Type*) [CommRing U] [Algebra T U]
    [Algebra S U] [IsScalarTower S T U] :
    (J.map (MvPolynomial.map (algebraMap S T))).map
      (MvPolynomial.map (algebraMap T U)) = J.map (MvPolynomial.map (algebraMap S U)) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- A basis neighborhood pulls back to the principal open of its image in the new base. -/
def baseChangeNeighborhood (r : PolynomialBasisNeighborhoods R I d w S J) :
    PolynomialBasisNeighborhoods R I d w T (J.map (MvPolynomial.map (algebraMap S T))) := by
  let _ := principalBaseChangeScalars T r.val
  let _ := principalBaseChangeTower (R := S) T r.val
  let _ := principalBaseChangeTower (R := R) T r.val
  refine ⟨algebraMap S T r.val, ?_⟩
  have h := (baseChangeIdeal R I d w (Localization.Away r.val)
    (Localization.Away (algebraMap S T r.val)) (neighborhoodIdeal R I d w S J r)).property
  rw [neighborhoodIdeal_baseChange_val] at h
  rw [polynomialIdeal_map_tower I S J T]
  exact h

/-- Classification on the pulled-back neighborhood is composition of the original parameter. -/
theorem baseChangeNeighborhood_classifyingMap
    (r : PolynomialBasisNeighborhoods R I d w S J) :
    neighborhoodClassifyingMap R I d w T (J.map (MvPolynomial.map (algebraMap S T)))
      (baseChangeNeighborhood R I d w S J T r) =
    ((principalBaseChangeMap T r.val).restrictScalars R).comp
      (neighborhoodClassifyingMap R I d w S J r) := by
  let _ := principalBaseChangeScalars T r.val
  let _ := principalBaseChangeTower (R := S) T r.val
  let _ := principalBaseChangeTower (R := R) T r.val
  change _ = (IsScalarTower.toAlgHom R (Localization.Away r.val)
    (Localization.Away (algebraMap S T r.val))).comp _
  rw [neighborhoodClassifyingMap_baseChange]
  apply congrArg (idealClassifyingMap R I d w _)
  apply Subtype.ext
  change (J.map (MvPolynomial.map (algebraMap S T))).map
    (MvPolynomial.map (algebraMap T (Localization.Away (algebraMap S T r.val)))) = _
  rw [neighborhoodIdeal_baseChange_val, polynomialIdeal_map_tower I S J T]

end FLT.Mazur.HilbertChart
