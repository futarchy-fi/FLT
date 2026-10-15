/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientBaseChange
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientImmersion
public import FLT.Mazur.PolygonOriginalBaseAdicKernel

/-!
# Exact parameter-power equations of the whole original adic relation

The complete relation's actual adic base change is cut out by the original
parameter power. These are equations before restricting to a node-pair open;
no identification of that further open restriction's kernel is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionLiftSpaceStructure completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "s" => completeIdentityActionLiftSpaceStructure K n h
local notation "t" => completeIdentityActionAmbientParameter K n h

/-- The whole original adic relation has exactly the extended original base-ideal power. -/
theorem completeIdentityAdicLiftSpaceMap_kernel (m : ℕ) :
    (completeIdentityActionAdicLiftSpaceMap K n h m).ker =
      ((BaseAdicThickening.baseIdeal (.of (PowerSeries K)) (parameterIdeal K)).comap (s)) ^
        (m + 1) := by
  rw [← (completeIdentityAdicLiftSpace_isPullback K n h m).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    baseToSeries_ker, FLT.Mazur.FCurve.idealSheaf_comap_pow]

variable (W : (completeIdentityActionLiftSpace K n h).affineOpens)
local notation "τ" => AffinePrincipalKernel.restriction W (t)

/-- Restriction of the complete parameter is its actual local coefficient function. -/
theorem completeIdentityActionAmbientParameter_restriction :
    (τ) = (s).appLE ⊤ W (by simp)
      ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv PowerSeries.X) := by
  change ((s).appTop ≫ AffinePrincipalKernel.restriction W)
    ((Scheme.ΓSpecIso (.of (PowerSeries K))).inv PowerSeries.X) = _
  have ht : (s).appLE ⊤ ⊤ (by simp) = (s).appTop := (s).appLE_eq_app
  rw [← ht, Scheme.Hom.appLE_map]

/-- Every affine patch of the whole adic relation has the literal parameter-power ideal. -/
theorem completeIdentityAdicLiftSpaceMap_affineKernel (m : ℕ) :
    (completeIdentityActionAdicLiftSpaceMap K n h m).ker.ideal W =
      Ideal.span {(τ) ^ (m + 1)} := by
  rw [completeIdentityAdicLiftSpaceMap_kernel, BaseAdicThickening.extendedPower_ideal,
    parameterIdeal, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  simp only [RingHom.comp_apply, map_pow]
  rw [completeIdentityActionAmbientParameter_restriction]

/-- The whole-adic section kernel is exact divisibility, without passing to a radical. -/
theorem completeIdentityAdicLiftSpaceMap_equation_iff (m : ℕ)
    (z : Γ(completeIdentityActionLiftSpace K n h, W)) :
    (completeIdentityActionAdicLiftSpaceMap K n h m).app W z = 0 ↔
      (τ) ^ (m + 1) ∣ z := by
  change z ∈ RingHom.ker
    ((completeIdentityActionAdicLiftSpaceMap K n h m).app W).hom ↔ _
  rw [← Scheme.Hom.ker_apply, completeIdentityAdicLiftSpaceMap_affineKernel,
    Ideal.mem_span_singleton]

end FLT.Mazur.PolygonInfinitesimalStages
