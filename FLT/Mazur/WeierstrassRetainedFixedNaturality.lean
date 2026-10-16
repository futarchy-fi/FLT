/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedDepthScale
public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioNaturality

/-!
# Coefficient squares for a fixed retained smoothing

The fixed quotient and the full scaled correction both follow the coefficient
map. The target smoothing is kept separate from every local root smoothing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (π τ q : R) (hq : π * q = τ) (π' τ' q' : S)
  (hπ : f π = π') (hτ : f τ = τ') (hqq : f q = q') (hq' : π' * q' = τ')
  (U : (ChartRing π)ˣ) (U' : (ChartRing π')ˣ)
local notation "F" => ringMap f π π' hπ
local notation "G" => ringMap f τ τ' hτ
variable (hU : Units.map (ringMap f π π' hπ).toMonoidHom U = U')
local notation "E" => retainedFixedSmoothingEvaluation π τ q hq U
local notation "E'" => retainedFixedSmoothingEvaluation π' τ' q' hq' U'

include hqq hU in
/-- Both whole corrected coordinates commute with the specified coefficient maps. -/
theorem retainedFixedSmoothingEvaluation_map :
    (F).comp (E).toRingHom = (E').toRingHom.comp G := by
  have hu := congrArg Units.val hU
  have hi := congrArg (fun z : (ChartRing π')ˣ ↦ (↑z⁻¹ : ChartRing π')) hU
  change F (U : ChartRing π) = (U' : ChartRing π') at hu
  change F (↑U⁻¹ : ChartRing π) = (↑(U')⁻¹ : ChartRing π') at hi
  apply chartRing_ringHom_ext
  · intro r
    change F (E (algebraMap R _ r)) = E' (G (algebraMap R _ r))
    rw [AlgHom.commutes, ringMap_scalar, ringMap_scalar, AlgHom.commutes]
  · change F (E (leftCoordinate τ)) = E' (G (leftCoordinate τ))
    rw [retainedFixedSmoothingEvaluation_left, ringMap_left,
      retainedFixedSmoothingEvaluation_left, RingHom.map_mul, RingHom.map_mul,
      ringMap_scalar, ringMap_left, hqq, hi]
  · change F (E (rightCoordinate τ)) = E' (G (rightCoordinate τ))
    rw [retainedFixedSmoothingEvaluation_right, ringMap_right,
      retainedFixedSmoothingEvaluation_right, RingHom.map_mul, ringMap_right, hu]

include hqq hU in
/-- The full fixed-target node map preserves the original coefficient square. -/
@[reassoc] theorem retainedFixedSmoothingChart_coefficients :
    Spec.map (CommRingCat.ofHom F) ≫ retainedFixedSmoothingChart π τ q hq U =
      retainedFixedSmoothingChart π' τ' q' hq' U' ≫ Spec.map (CommRingCat.ofHom G) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (retainedFixedSmoothingEvaluation_map f π τ q hq π' τ' q' hπ hτ hqq hq' U U' hU)

/-- Recursive coefficient scales commute with every coefficient homomorphism. -/
theorem retainedDepthScale_map (q α : Rˣ) (i : ℕ) :
    Units.map f.toMonoidHom (retainedDepthScale q α i) =
      retainedDepthScale (Units.map f.toMonoidHom q) (Units.map f.toMonoidHom α) i := by
  simp only [retainedDepthScale, map_mul, map_pow, map_inv]

include hU in
/-- Coefficient scaling preserves the already proved full correction square. -/
theorem retainedScaledCorrectionUnit_coefficients (α : Rˣ) :
    Units.map (F).toMonoidHom (retainedScaledCorrectionUnit π α U) =
      retainedScaledCorrectionUnit π' (Units.map f.toMonoidHom α) U' := by
  have hu := congrArg Units.val hU
  apply Units.ext
  change F (algebraMap R _ (α : R) * (U : ChartRing π)) =
    algebraMap S _ (f (α : R)) * (U' : ChartRing π')
  rw [map_mul, ringMap_scalar]
  exact congrArg (fun v ↦ algebraMap S _ (f (α : R)) * v) hu

end FLT.Mazur.WeierstrassModificationX
