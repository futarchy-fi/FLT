/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelCohomologySum
public import FLT.Mazur.BaseAdicReesModelHZeroInclusions
public import FLT.Mazur.NoetherianSumCechInclusion

/-!
# Original power inclusions in all degrees of model cohomology

The original sheaf inclusion identity passes through the all-degree additive
comparison, independently of the finite affine cover chosen to construct it.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open scoped DirectSum

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) (J : Ideal R)
  [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso
  modelDirectImageCohomologyEquiv

/-- Every original power inclusion retains its degree in the all-degree comparison. -/
lemma modelPowerCohomologySumEquiv_inclusion (q n : ℕ)
    (s : ModuleRingH (baseCohomologyScalars f) (modelPowerSheaves f J M n) q) :
    modelPowerCohomologySumEquiv f J M q (moduleHMap (modelPowerInclusion f J M n) q s) =
      DirectSum.lof R ℕ _ n s := by
  let _ := modelPowerSum_isQuasicoherent f J M
  let h := Chow.exists_finite_affine_cover_all_generics X
  let ι := h.choose
  let _ : Fintype ι := h.choose_spec.choose
  let U := h.choose_spec.choose_spec.choose
  have hU := h.choose_spec.choose_spec.choose_spec
  change NoetherianModuleSum.cohomologyEquiv (modelPowerSheaves f J M) U
    hU.1 hU.2.2.1 q
      (moduleHMap (modelPointwiseSumIso f J M).hom q
        (moduleHMap (modelPowerInclusion f J M n) q s)) = _
  rw [← LinearMap.comp_apply, ← moduleHMap_comp, modelPowerInclusion_pointwiseSum]
  exact NoetherianModuleSum.cohomologyEquiv_inclusion _ U hU.1 hU.2.2.1 q n s

/-- Original power cohomology classes assemble into the actual global model in every degree. -/
def modelPowerToModelEquiv (q : ℕ) :
    PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q ≃+
      ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) q :=
  (modelPowerCohomologySumEquiv f J M q).symm.trans
    (modelDirectImageCohomologyEquiv f J M q)

/-- The assembly is exactly the inverse of the existing all-degree model comparison. -/
lemma modelPowerToModelEquiv_eq (q : ℕ) :
    modelPowerToModelEquiv f J M q = (modelCohomologyPowerSumEquiv f J M q).symm := rfl

/-- Each original power class maps through the actual model degree inclusion. -/
lemma modelPowerToModelEquiv_of (q n : ℕ)
    (s : ModuleRingH (baseCohomologyScalars f) (modelPowerSheaves f J M n) q) :
    modelPowerToModelEquiv f J M q (DirectSum.lof R ℕ _ n s) =
      modelDirectImageCohomologyEquiv f J M q
        (moduleHMap (modelPowerInclusion f J M n) q s) := by
  change modelDirectImageCohomologyEquiv f J M q
    ((modelPowerCohomologySumEquiv f J M q).symm _) = _
  apply congrArg (modelDirectImageCohomologyEquiv f J M q)
  exact (modelPowerCohomologySumEquiv f J M q).symm_apply_eq.mpr
    (modelPowerCohomologySumEquiv_inclusion f J M q n s).symm

end FLT.Mazur.BaseAdicRees
