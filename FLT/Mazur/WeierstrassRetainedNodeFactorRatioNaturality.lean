/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorNaturality

/-!
# The full retained comparison commutes with the coefficient square

The same divisor is transported along the coefficient map. Both coordinates
retain the entire correction and the exact normalized smoothing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
local notation "F" => (ringMap f π (f π) rfl : ChartRing π →+* ChartRing (f π))
variable (hI : IsNilpotent I) (hJ : IsNilpotent J) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "V" => retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "V'" => retainedFactorCorrectionUnit (W.map f) (f π) (f s) (f c3) (f c4)
  (f c6) J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

local notation "τ" => initialTangentSmoothing W ha s
local notation "τ'" => initialTangentSmoothing (W.map f) (ha.map f) (f s)
local notation "G" => ringMap f τ τ' (initialTangentSmoothing_map W ha s f)
variable (d : R) (hd : s = π * d)
local notation "E" => retainedFactorRatioEvaluation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd
local notation "E'" => retainedFactorRatioEvaluation (W.map f) (f π) (f s) (f c3) (f c4)
  (f c6) J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) (f d)
  (Eq.trans (congrArg f hd) (map_mul f π d))
attribute [local irreducible] retainedFactorCorrectionUnit

/-- The full retained algebra square preserves both coordinates and all original coefficients. -/
theorem retainedFactorRatioEvaluation_map :
    (F).comp (E).toRingHom = (E').toRingHom.comp G := by
  have hv := retainedFactorCorrectionUnit_map f W π s c3 c4 c6 I J hf
    hI hJ ha hs h2 h3 h4 h6
  have hvi := congrArg (fun z : (ChartRing (f π))ˣ ↦ (↑z⁻¹ : ChartRing (f π))) hv
  have hva := congrArg Units.val hv
  have hi := congrArg (fun z : Sˣ ↦ (↑z⁻¹ : S)) (initialTangentUnit_map W ha f)
  apply chartRing_ringHom_ext
  · intro r
    change F (E (algebraMap R _ r)) = E' (G (algebraMap R _ r))
    rw [AlgHom.commutes, ringMap_scalar, ringMap_scalar, AlgHom.commutes]
  · change F (E (leftCoordinate τ)) = E' (G (leftCoordinate τ))
    rw [retainedFactorRatioEvaluation_left, ringMap_left, retainedFactorRatioEvaluation_left,
      RingHom.map_mul, RingHom.map_mul, ringMap_left, ringMap_scalar]
    change F (↑V⁻¹ : ChartRing π) = (↑(V')⁻¹ : ChartRing (f π)) at hvi
    rw [hvi, RingHom.map_mul, RingHom.map_pow]
    change f (↑(zeroInitialTangentUnit W ha)⁻¹ : R) =
      (↑(zeroInitialTangentUnit (W.map f) (ha.map f))⁻¹ : S) at hi
    rw [hi]
  · change F (E (rightCoordinate τ)) = E' (G (rightCoordinate τ))
    rw [retainedFactorRatioEvaluation_right, ringMap_right, retainedFactorRatioEvaluation_right,
      RingHom.map_mul, ringMap_right]
    change F (V : ChartRing π) = (V' : ChartRing (f π)) at hva
    rw [hva]

/-- The entire retained chart commutes with the original normalized coefficient square. -/
@[reassoc] theorem retainedFactorRatioChart_coefficients :
    Spec.map (CommRingCat.ofHom F) ≫
      retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd =
    retainedFactorRatioChart (W.map f) (f π) (f s) (f c3) (f c4) (f c6) J hJ
      (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) (f d)
      (Eq.trans (congrArg f hd) (map_mul f π d)) ≫ Spec.map (CommRingCat.ofHom G) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (retainedFactorRatioEvaluation_map f W π s c3 c4 c6 I J hf
    hI hJ ha hs h2 h3 h4 h6 d hd)

end FLT.Mazur.WeierstrassModificationX
