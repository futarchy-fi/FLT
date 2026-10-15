/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePrincipalKernel
public import FLT.Mazur.PolygonCompleteIdentityGenericAmbientKernel
public import FLT.Mazur.PowerSeriesFractionGenericOpen

/-!
# The full original graph equations are complete-ambient parameter torsion

The entire generic ambient relation is the generic smooth graph. Its open
inclusion is exactly the nonvanishing parameter locus, so the full original
graph kernel on any affine patch consists precisely of functions killed by
a power of the original complete parameter. This calculation precedes adic
specialization and does not assert saturation after adding the parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "Y" => completeIdentityActionLiftSpace K n h
local notation "s" => completeIdentityActionLiftSpaceStructure K n h
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "g" => completeIdentityActionGenericSmoothGraph K n h
local notation "r" => completeIdentityActionGenericAmbientInclusion K n h

/-- The original complete parameter as an actual global function on the entire lifting space. -/
def completeIdentityActionAmbientParameter : Γ((Y), ⊤) :=
  (s).appTop ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv PowerSeries.X)
local notation "t" => completeIdentityActionAmbientParameter K n h

/-- Its nonvanishing open is exactly the original generic coefficient open. -/
theorem completeIdentityActionAmbientParameter_open :
    (Y).basicOpen (t) = (s) ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K) := by
  exact (Scheme.preimage_basicOpen (s)
    ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv PowerSeries.X)).symm.trans
      (congrArg (fun U : (Spec (.of (PowerSeries K))).Opens ↦ (s) ⁻¹ᵁ U)
        (basicOpen_eq_of_affine (R := CommRingCat.of (PowerSeries K)) PowerSeries.X))

/-- The full original smooth-graph kernel is the full principal-open kernel. -/
theorem completeIdentityActionSmoothGraph_parameterKernel :
    (f).ker = ((Y).basicOpen (t)).ι.ker := by
  rw [← completeIdentityActionGenericAmbient_kernel,
    completeIdentityActionAmbientParameter_open]
  rw [show (r) = (PowerSeriesFractionGenericOpen.fiberIso K (s)).hom ≫
      ((s) ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)).ι from
        (PowerSeriesFractionGenericOpen.fiberIso_inclusion K (s)).symm,
    Scheme.Hom.ker_comp_of_isIso]

variable (W : (completeIdentityActionLiftSpace K n h).affineOpens)
local notation "ρ" => AffinePrincipalKernel.restriction W

/-- An actual local graph equation is exactly a function killed by a complete parameter power. -/
theorem completeIdentityActionSmoothGraph_equation_iff_parameter_torsion (z : Γ((Y), W)) :
    (f).app W z = 0 ↔ ∃ d : ℕ, (ρ) (t) ^ d * z = 0 := by
  change z ∈ RingHom.ker ((f).app W).hom ↔ _
  rw [← Scheme.Hom.ker_apply, completeIdentityActionSmoothGraph_parameterKernel,
    Scheme.Hom.ker_apply]
  exact AffinePrincipalKernel.equation_iff (t) W z

/-- The generic smooth-graph equations have the same concrete power-torsion description. -/
theorem completeIdentityActionGenericSmoothGraph_equation_iff_parameter_torsion
    (z : Γ((Y), W)) : (g).app W z = 0 ↔ ∃ d : ℕ, (ρ) (t) ^ d * z = 0 := by
  change z ∈ RingHom.ker ((g).app W).hom ↔ _
  rw [← completeIdentityActionSmoothGraph_affineKernel]
  exact completeIdentityActionSmoothGraph_equation_iff_parameter_torsion K n h W z

end FLT.Mazur.PolygonInfinitesimalStages
