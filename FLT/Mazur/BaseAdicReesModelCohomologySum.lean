/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelGlobalSections
public import FLT.Mazur.BaseAdicReesModelDirectImageCohomology
public import FLT.Mazur.NoetherianSumCechCohomology
public import FLT.Mazur.ChowDenseAffineCover
public import FLT.Mazur.CohomologyImageReesModule

/-!
# All-degree additive comparison with the actual Rees model

Noetherian compactness supplies an actual finite affine cover. The original
sectionwise sum and its Cech complex compute the original power cohomologies
in every degree. Compatibility with the original homogeneous Rees action
still requires naturality of the direct-sum homology comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

attribute [local irreducible] modelPushforward modelPointwiseSumIso

omit [X.IsSeparated] in
/-- The original sectionwise sum is quasi-coherent because it is the actual affine direct image. -/
lemma modelPowerSum_isQuasicoherent :
    (NoetherianModuleSum.sum (modelPowerSheaves f J M)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (modelPointwiseSumIso f J M) inferInstance

/-- The actual direct image has the original additive power-cohomology sum in every degree. -/
def modelPowerCohomologySumEquiv (q : ℕ) :
    ModuleRingH (baseCohomologyScalars f) (modelPushforward f J M) q ≃+
      PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q := by
  let _ := modelPowerSum_isQuasicoherent f J M
  let h := Chow.exists_finite_affine_cover_all_generics X
  let ι := h.choose
  let _ : Fintype ι := h.choose_spec.choose
  let U := h.choose_spec.choose_spec.choose
  have hU := h.choose_spec.choose_spec.choose_spec
  exact (((moduleRingHFunctor (baseCohomologyScalars f) q).mapIso
    (modelPointwiseSumIso f J M)).toLinearEquiv.toAddEquiv).trans
    (NoetherianModuleSum.cohomologyEquiv (modelPowerSheaves f J M) U hU.1 hU.2.2.1 q)

/-- Cohomology of the actual global model has the same additive original-power coordinates. -/
def modelCohomologyPowerSumEquiv (q : ℕ) :
    ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) q ≃+
      PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q :=
  (modelDirectImageCohomologyEquiv f J M q).symm.trans
    (modelPowerCohomologySumEquiv f J M q)

end FLT.Mazur.BaseAdicRees
