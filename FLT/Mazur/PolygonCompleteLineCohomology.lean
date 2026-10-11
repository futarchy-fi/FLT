/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalClosedLineCohomology
public import FLT.Mazur.PolygonCompleteStructureCohomology

/-!
# Transfer of actual closed line vanishing to the complete polygon family

The regular parameter quotient is compared with the original polygon
inclusion, retaining the given line coefficient. Proper finiteness and
Nakayama then transfer closed vanishing to the original complete family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve IdealPowerScalarLift Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj K n h).Modules) (hL : LocallyFreeRankOne L)

/-- The original line's parameter quotient is its actual original closed pullback. -/
def completeLineScalarQuotientClosedIso :
    cokernel (scalarEnd L
      (baseCohomologyScalars (exactVeroneseProjToBase K n h) PowerSeries.X)) ≅
        (Scheme.Modules.pushforward (completeClosedFiberInclusion K n h)).obj
          ((Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj L) := by
  let _ := completeParameter_scalarEnd_mono K n h
  exact PrincipalClosedLineCohomology.cokernelIso (compatibleProjAdicIdeal K n h)
    L hL _ (completeParameter_ideal K n h) ≪≫
      IsomorphicClosedPullback.overIso (completeClosedIdealIso K n h) _ L _
        (completeClosedIdealIso_hom_ι K n h)

include hL in
/-- Vanishing on the original polygon forces vanishing of the actual complete line. -/
theorem completeLine_vanishing_of_closed (q : ℕ)
    (hq : Subsingleton (ModuleH
      ((Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj L) q)) :
    Subsingleton (ModuleRingH (baseCohomologyScalars (exactVeroneseProjToBase K n h))
      L q) := by
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := hL.isFinitePresentation
  let _ := (hL.pullback (completeClosedFiberInclusion K n h)).isFinitePresentation
  let _ := completeParameter_scalarEnd_mono K n h
  let _ := LineScalarMonicity.scalarEnd_mono L
    (baseCohomologyScalars (exactVeroneseProjToBase K n h) PowerSeries.X) hL
  let _ := proper_coherent_hasFiniteRingCohomology (exactVeroneseProjToBase K n h) L q
  let ρ := baseCohomologyScalars (exactVeroneseProjToBase K n h)
  let e := ((moduleRingHFunctor ρ q).mapIso
    (completeLineScalarQuotientClosedIso K n h L hL)).toLinearEquiv.trans
      (closedPushforwardRingHEquiv (completeClosedFiberInclusion K n h) _ ρ q)
  let _ : Subsingleton (ModuleH (cokernel (scalarEnd L (ρ PowerSeries.X))) q) :=
    ⟨fun x y ↦ e.injective (hq.elim _ _)⟩
  apply PrincipalScalarCohomology.finite_vanishing L ρ PowerSeries.X _ q
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    ← PowerSeries.ker_coeff_eq_max_ideal]
  exact PowerSeries.constantCoeff_X

end FLT.Mazur.PolygonInfinitesimalStages
