/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFieldFibers

/-!
# The complete one-gon smoothing is a classified genus-one family

Combine the proved field-fiber geometry with properness, flatness, constants
and actual cohomology. The contract persists under arbitrary scheme base change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open FCurve FCurve.CurveFiberHypotheses FCurve.DRFiberClassification
variable (K : Type) [Field K]

/-- Every geometric fiber of the explicit complete family is smooth or the original one-gon. -/
theorem complete_classifiedGeometricFibers :
    ClassifiedGeometricFibers (family (PowerSeries.X : PowerSeries K)).hom :=
  ⟨fun L _ _ s _ p q hs ↦ completeCartesian_classified K L s p q hs⟩

/-- Every geometric fiber has the required nodal core, constants and actual genus one. -/
theorem complete_genusOneGeometricFibers :
    let _ := family_proper (PowerSeries.X : PowerSeries K)
    NodalGenusOneGeometricFibers (family (PowerSeries.X : PowerSeries K)).hom := by
  let _ := family_proper (PowerSeries.X : PowerSeries K)
  constructor
  intro L _ _ s Y p q hs
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  exact ⟨(completeCartesian_classified K L s p q hs).toNodalFiberCore,
    completeCartesian_constantSections K L s p q hs, completeCartesianH1_finrank K L s p q hs⟩

/-- The actual complete one-gon smoothing satisfies the full classified genus-one contract. -/
theorem complete_classifiedGenusOneFamily :
    ClassifiedGenusOneFamily (family (PowerSeries.X : PowerSeries K)).hom :=
  ⟨⟨family_proper _, family_flat _, family_lfp _⟩,
    complete_classifiedGeometricFibers K, complete_genusOneGeometricFibers K⟩

/-- The full constructed family contract persists under every scheme base change. -/
theorem completeBaseChange_classifiedGenusOneFamily {S : Scheme}
    (s : S ⟶ Spec (.of (PowerSeries K))) :
    ClassifiedGenusOneFamily (pullback.snd (family (PowerSeries.X : PowerSeries K)).hom s) :=
  (complete_classifiedGenusOneFamily K).baseChange s

/-- The actual constant-coefficient closed fiber retains the original nodal classification. -/
theorem closedFiber_classified :
    ClassifiedFiberCore (pullback.snd (family (PowerSeries.X : PowerSeries K)).hom
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K))))) :=
  completeCartesian_classified K K _ _ _ (IsPullback.of_hasPullback _ _)

/-- The actual constant-coefficient closed fiber has one-dimensional first cohomology. -/
theorem closedFiberH1_finrank :
    Module.finrank K (H1 (pullback.snd (family (PowerSeries.X : PowerSeries K)).hom
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))))) = 1 :=
  completeCartesianH1_finrank K K _ _ _ (IsPullback.of_hasPullback _ _)

end FLT.Mazur.OneGonSmoothing
