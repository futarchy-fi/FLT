/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartSocleVanishing

/-!
# Original-base flatness of the full first error algebra

The constructed comparison isomorphism transports the original chart's
flat structure to the finite error algebra. The coefficient map is the
actual source-node map composed with the original Laurent coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (e)
local notation "E" => completeIdentityFirstErrorAlgebra K n h (0 : Fin n)
local notation "c" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "a" => completeIdentityActionGraphAdicChartStructure K n h 1 0 0
local notation "j" => completeIdentityFirstGraphToChart K n h

/-- Cache the original finite error ring structure for coefficient comparisons. -/
local instance firstErrorOriginalFlatCommRing : CommRing (E) := inferInstance

/-- Original coefficients enter the error algebra through its unchanged source-node map. -/
def completeIdentityFirstErrorOriginalScalars : Ring K 1 →+* (E) :=
  (completeIdentityFirstGraphSource K n h 0).toRingHom.comp
    ((algebraMap (S) (B)).comp (c))

/-- The full comparison intertwines exactly these original coefficient morphisms. -/
@[reassoc] theorem completeIdentityFirstGraphToChart_originalStructure :
    (j) ≫ (a) = Spec.map (CommRingCat.ofHom
      (completeIdentityFirstErrorOriginalScalars K n h)) := by
  rw [← completeIdentityActionGraphAdicChartSource_structure K n h 1 0 0,
    completeIdentityFirstGraphToChart_source_assoc,
    firstNodeParameterIso_hom_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- Flatness transfers through the proved full comparison over the actual original base. -/
theorem completeIdentityFirstErrorOriginalScalars_flat :
    (completeIdentityFirstErrorOriginalScalars K n h).Flat := by
  let _ : IsIso (j) := completeIdentityFirstGraphToChart_isIso K n h
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (completeIdentityFirstErrorOriginalScalars K n h))).mp
  rw [← completeIdentityFirstGraphToChart_originalStructure]
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
