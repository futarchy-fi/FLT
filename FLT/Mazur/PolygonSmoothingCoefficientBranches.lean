/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBaseChange
public import FLT.Mazur.PolygonSmoothingOverlapGraph
public import FLT.Mazur.LaurentTensor

/-!
# Coefficient change on complete cyclic edges

The actual coefficient projection commutes with both full Laurent branches,
including inversion on the incoming edge. No nilpotence is needed here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial TensorProduct

universe u

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

attribute [local irreducible] baseChangeEquiv

/-- The chart coefficient map with its original scalar structure retained. -/
def coefficientAlgHom (t : R) : ChartRing t →ₐ[R] ChartRing (algebraMap R S t) where
  __ := coefficientMap R S t
  commutes' r := by
    change baseChangeEquiv R S t (1 ⊗ₜ[R] algebraMap R (ChartRing t) r) = _
    have he : (1 : S) ⊗ₜ[R] algebraMap R (ChartRing t) r =
        algebraMap R S r ⊗ₜ[R] (1 : ChartRing t) := by
      simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul]
    rw [he]
    exact (baseChangeEquiv R S t).commutes (algebraMap R S r)

@[simp] theorem coefficientAlgHom_left (t : R) :
    coefficientAlgHom R S t (leftCoordinate t) = leftCoordinate (algebraMap R S t) :=
  coefficientMap_left R S t

@[simp] theorem coefficientAlgHom_right (t : R) :
    coefficientAlgHom R S t (rightCoordinate t) = rightCoordinate (algebraMap R S t) :=
  coefficientMap_right R S t

/-- The spectrum projection of the actual chart coefficient map. -/
def chartCoefficient (t : R) : chart S (algebraMap R S t) ⟶ chart R t :=
  Spec.map (CommRingCat.ofHom (coefficientMap R S t))

/-- The full edge torus coefficient projection fixes its Laurent coordinate. -/
def edgeCoefficient : branchTorus S ⟶ branchTorus R :=
  Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap (algebraMap R S)))

/-- Outgoing Laurent restriction commutes with the chart coefficient map. -/
theorem leftLaurent_coefficient (t : R) :
    ((leftLaurentMap (algebraMap R S t)).restrictScalars R).comp
      (coefficientAlgHom R S t) = (LaurentTensor.coeff R S).comp (leftLaurentMap t) := by
  apply chartRing_hom_ext t <;>
    simp [LaurentTensor.coeff]

/-- Incoming inverse-coordinate restriction commutes with coefficient change. -/
theorem precedingLaurent_coefficient (t : R) :
    ((precedingLaurentMap S (algebraMap R S t)).restrictScalars R).comp
      (coefficientAlgHom R S t) =
        (LaurentTensor.coeff R S).comp (precedingLaurentMap R t) := by
  apply chartRing_hom_ext t <;>
    simp [precedingLaurentMap, LaurentTensor.coeff]

/-- The whole outgoing branch square commutes. -/
@[reassoc] theorem leftBranch_coefficient (t : R) :
    leftBranchOpen S (algebraMap R S t) ≫ chartCoefficient R S t =
      edgeCoefficient R S ≫ leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec, leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (leftLaurent_coefficient R S t))

/-- The whole incoming branch square, with its inverse coordinate, commutes. -/
@[reassoc] theorem precedingBranch_coefficient (t : R) :
    precedingBranch S (algebraMap R S t) ≫ chartCoefficient R S t =
      edgeCoefficient R S ≫ precedingBranch R t := by
  rw [precedingBranch_eq_spec, precedingBranch_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (precedingLaurent_coefficient R S t))

/-- The chart projection lies over the specified coefficient-ring morphism. -/
@[reassoc] theorem chartCoefficient_base (t : R) :
    chartCoefficient R S t ≫ chartStructure R t =
      chartStructure S (algebraMap R S t) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (coefficientAlgHom R S t).comp_algebraMap

end FLT.Mazur.PolygonSmoothing
