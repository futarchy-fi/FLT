/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialBasisCover
public import FLT.Mazur.HilbertChartClassificationNaturality

/-!
# Compatibility of the local Hilbert chart parameters

On every common scalar extension of two principal basis neighborhoods,
the actual extended ideals agree and hence their classifying parameters agree.
This uses classification of ideals, not a chosen quotient trivialization.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable (R : Type*) [CommRing R] (I : Type*) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]

/-- Localizing first and then extending scalars gives the same actual ambient ideal. -/
theorem neighborhoodIdeal_baseChange_val (r : PolynomialBasisNeighborhoods R I d w S J)
    [Algebra (Localization.Away r.val) T] [IsScalarTower S (Localization.Away r.val) T]
    [IsScalarTower R (Localization.Away r.val) T] :
    (baseChangeIdeal R I d w (Localization.Away r.val) T
      (neighborhoodIdeal R I d w S J r)).val =
      J.map (MvPolynomial.map (algebraMap S T)) := by
  change (J.map (MvPolynomial.map (algebraMap S (Localization.Away r.val)))).map
    (MvPolynomial.map (algebraMap (Localization.Away r.val) T)) = _
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

omit [Algebra S T] in
/-- The local classifying parameter remains the parameter of the actual extended ideal. -/
theorem neighborhoodClassifyingMap_baseChange (r : PolynomialBasisNeighborhoods R I d w S J)
    [Algebra (Localization.Away r.val) T] [IsScalarTower R (Localization.Away r.val) T] :
    (IsScalarTower.toAlgHom R (Localization.Away r.val) T).comp
      (neighborhoodClassifyingMap R I d w S J r) =
      idealClassifyingMap R I d w T (baseChangeIdeal R I d w (Localization.Away r.val) T
        (neighborhoodIdeal R I d w S J r)) :=
  (idealClassifyingMap_baseChangeIdeal R I d w (Localization.Away r.val) T
    (neighborhoodIdeal R I d w S J r)).symm

/-- Two neighborhoods yield the same parameter on every common base extension. -/
theorem neighborhoodClassifyingMap_agree (r s : PolynomialBasisNeighborhoods R I d w S J)
    [Algebra (Localization.Away r.val) T] [Algebra (Localization.Away s.val) T]
    [IsScalarTower S (Localization.Away r.val) T]
    [IsScalarTower S (Localization.Away s.val) T]
    [IsScalarTower R (Localization.Away r.val) T]
    [IsScalarTower R (Localization.Away s.val) T] :
    (IsScalarTower.toAlgHom R (Localization.Away r.val) T).comp
      (neighborhoodClassifyingMap R I d w S J r) =
    (IsScalarTower.toAlgHom R (Localization.Away s.val) T).comp
      (neighborhoodClassifyingMap R I d w S J s) := by
  rw [neighborhoodClassifyingMap_baseChange, neighborhoodClassifyingMap_baseChange]
  apply congrArg (idealClassifyingMap R I d w T)
  apply Subtype.ext
  rw [neighborhoodIdeal_baseChange_val, neighborhoodIdeal_baseChange_val]

end FLT.Mazur.HilbertChart
