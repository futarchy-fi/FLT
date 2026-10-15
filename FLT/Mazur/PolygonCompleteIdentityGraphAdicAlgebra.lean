/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Literal quotient coordinate rings for the original adic graph charts

The actual graph-chart functions are the quotient of the original cubic
node-relation functions by the full pulled-back complete graph ideal. The
coefficient homomorphism is flat over the original truncated ring itself.
No identification with the finite branch-image algebra is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "H" => completeIdentityActionGraphAdicChart K n h m i j
local notation "R" => completeIdentityActionAdicChartSpace K n h m i j
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h m i j
local notation "s" => completeIdentityActionGraphAdicChartStructure K n h m i j

/-- The full affine defining ideal, obtained from the actual chart restriction map. -/
def completeIdentityActionGraphAdicChartRingIdeal : Ideal Γ((R), ⊤) :=
  RingHom.ker (c).appTop.hom

/-- Every actual graph-chart function lifts to the original node-relation affine ring. -/
theorem completeIdentityActionGraphAdicChart_appTop_surjective :
    Function.Surjective (c).appTop :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine (c)).2

/-- The literal quotient recovers all graph-chart functions, including nilpotents. -/
def completeIdentityActionGraphAdicChartQuotientEquiv :
    Γ((R), ⊤) ⧸ completeIdentityActionGraphAdicChartRingIdeal K n h m i j ≃+* Γ((H), ⊤) :=
  RingHom.quotientKerEquivOfSurjective
    (completeIdentityActionGraphAdicChart_appTop_surjective K n h m i j)

/-- The quotient comparison is the original closed restriction on every ambient function. -/
theorem completeIdentityActionGraphAdicChartQuotientEquiv_mk (z : Γ((R), ⊤)) :
    completeIdentityActionGraphAdicChartQuotientEquiv K n h m i j (Ideal.Quotient.mk _ z) =
      (c).appTop z := rfl

/-- The chart's coefficient map uses the original truncated ring, without a chosen substitute. -/
def completeIdentityActionGraphAdicChartScalars : Ring K m →+* Γ((H), ⊤) :=
  (s).appTop.hom.comp (Scheme.ΓSpecIso (.of (Ring K m))).inv.hom

/-- The actual chart coordinate ring is flat over the unchanged truncated coefficient ring. -/
theorem completeIdentityActionGraphAdicChartScalars_flat :
    (completeIdentityActionGraphAdicChartScalars K n h m i j).Flat := by
  have hb : (Scheme.ΓSpecIso (.of (Ring K m))).inv.hom.Flat :=
    RingHom.Flat.of_bijective
      (Scheme.ΓSpecIso (.of (Ring K m))).symm.commRingCatIsoToRingEquiv.bijective
  exact hb.comp (s).flat_appTop

/-- The ring ideal is exactly the full ideal sheaf's affine value. -/
theorem completeIdentityActionGraphAdicChartRingIdeal_eq :
    completeIdentityActionGraphAdicChartRingIdeal K n h m i j =
      (c).ker.ideal ⟨⊤, isAffineOpen_top (R)⟩ := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp [completeIdentityActionGraphAdicChartRingIdeal]

end FLT.Mazur.PolygonInfinitesimalStages
