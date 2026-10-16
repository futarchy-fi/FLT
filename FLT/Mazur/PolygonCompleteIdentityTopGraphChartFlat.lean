/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartBranchQuotient
public import FLT.Mazur.PolygonCompleteIdentityTopGraphOriginalFlat
public import FLT.Mazur.PolygonStageNodeParameterStructure
public import FLT.Mazur.PolygonCompleteIdentitySecondCorrection

/-!
# The precise geometric kernel required for higher original-base flatness

The constructed chart comparison preserves the actual original coefficient
map. Killing its full two-puncture kernel therefore transfers flatness from
the literal chart. The kernel vanishing is an explicit remaining obligation.
At the second correction the already-proved first law supplies finiteness.
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
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "f" => completeIdentityTopGraphToChart K n h m
local notation "a" => completeIdentityActionGraphAdicChartStructure K n h (m + 1) 0 0
local notation "c" => completeIdentityTopGraphOriginalScalars K n h 0 m

/-- The constructed comparison retains every scalar of the actual original base. -/
@[reassoc] theorem completeIdentityTopGraphToChart_originalStructure :
    (f) ≫ (a) = Spec.map (CommRingCat.ofHom (c)) := by
  rw [← completeIdentityActionGraphAdicChartSource_structure K n h (m + 1) 0 0,
    completeIdentityTopGraphToChart_source_assoc,
    stageNodeParameterIso_hom_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (topNodeGraphSource K[T;T⁻¹] m
    (completeIdentityTopActionUnit K n h 0 m)
    (completeIdentityTopActionReciprocalUnit K n h 0 m)).commutes
      (stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1) r)

/-- Vanishing of the whole actual chart kernel identifies the original graph and chart. -/
theorem completeIdentityTopGraphToChart_isIso_of_kernel
    (hk : RingHom.ker (SpectrumGlobalRange.ringHom (f)) = ⊥) : IsIso (f) := by
  have hi := (RingHom.injective_iff_ker_eq_bot _).mpr hk
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  exact Function.Injective.of_comp hi

/-- Full kernel vanishing transfers flatness over the unchanged original coefficient map. -/
theorem completeIdentityTopGraphOriginalScalars_flat_of_kernel
    (hk : RingHom.ker (SpectrumGlobalRange.ringHom (f)) = ⊥) : (c).Flat := by
  let _ := completeIdentityTopGraphToChart_isIso_of_kernel K n h m hk
  apply (@Flat.SpecMap_iff _ _ (CommRingCat.ofHom (c))).mp
  rw [← completeIdentityTopGraphToChart_originalStructure]
  infer_instance

/-- The first original law proves the second-stage comparison finite without a new premise. -/
theorem completeIdentitySecondGraphToChart_finite :
    IsFinite (completeIdentityTopGraphToChart K n h 1) :=
  completeIdentityTopGraphToChart_finite K n h 1
    (completeIdentityFiniteMulDefect_firstPositive K n h)

end FLT.Mazur.PolygonInfinitesimalStages
