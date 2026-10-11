/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedH1Scalars
public import FLT.Mazur.ModuleCohomologyScalarRestriction
public import FLT.Mazur.PrincipalResidueTensor

/-!
# Rank one for the original complete family

Residue tensor base change of the original finite free H1 is its actual
closed H1. The polygon incidence computation therefore determines its rank.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The residue tensor product computes actual closed H1 over the residue field. -/
def completeH1ResidueTensorEquiv :
    let _ : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
    K ⊗[PowerSeries K] ModuleRingH
      (baseCohomologyScalars (exactVeroneseProjToBase K n h))
      (structureModule (exactVeroneseProj K n h)) 1 ≃ₗ[K]
        ModuleRingH (completeClosedFieldScalars K n h)
          (structureModule (compatibleProjAdicIdeal K n h).subscheme) 1 := by
  let _ : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
  let M := ModuleRingH (baseCohomologyScalars (exactVeroneseProjToBase K n h))
    (structureModule (exactVeroneseProj K n h)) 1
  let N := ModuleRingH (completeClosedFieldScalars K n h)
    (structureModule (compatibleProjAdicIdeal K n h).subscheme) 1
  let _ : Module (PowerSeries K) N := Module.compHom N PowerSeries.constantCoeff
  let _ : IsScalarTower (PowerSeries K) K N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have hk : RingHom.ker (algebraMap (PowerSeries K) K) =
      Ideal.span {(PowerSeries.X : PowerSeries K)} := by
    ext a
    exact (PowerSeries.X_dvd_iff).symm.trans (Ideal.mem_span_singleton).symm
  let e := (PrincipalResidueTensor.principalTensorEquiv
    PowerSeries.constantCoeff_surj M PowerSeries.X hk).trans
      ((completeStructureH1ReductionEquiv K n h).trans
        (moduleRingHFactorEquiv (completeClosedRingScalars K n h)
          PowerSeries.constantCoeff (completeClosedFieldScalars K n h)
          (completeClosedRingScalars_factor K n h) _ 1))
  exact PrincipalResidueTensor.extendEquiv PowerSeries.constantCoeff_surj e

/-- The original complete family's actual finite free H1 has rank one. -/
theorem completeStructureH1_finrank :
    Module.finrank (PowerSeries K) (ModuleRingH
      (baseCohomologyScalars (exactVeroneseProjToBase K n h))
      (structureModule (exactVeroneseProj K n h)) 1) = 1 := by
  let _ : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
  let _ := completeStructureH1_free K n h
  rw [← Module.finrank_baseChange (R := K)]
  exact (completeH1ResidueTensorEquiv K n h).finrank_eq.trans
    (completeClosedH1_finrank K n h)

end FLT.Mazur.PolygonInfinitesimalStages
