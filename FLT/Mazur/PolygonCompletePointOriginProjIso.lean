/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginAmple
public import FLT.Mazur.ProperAmpleSectionProjIso
public import FLT.Mazur.SectionGradedProjStructuralMap

/-!
# The original cubic is its intrinsic origin-line section Proj

The canonical reconstruction uses all tensor degrees of the original origin
line, over the original complete base, and retains every cubic coordinate open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedSum SectionGradedProjConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "A" => originDivisorLine (W) 1
local notation "hA" => completePointOriginLine_positivePowerGenerated K n h i

local instance completePointOriginProjLineFact : Fact (LocallyFreeRankOne (A)) :=
  ⟨completePointOriginLine_rankOne K n h i 1⟩

/-- The actual canonical section map reconstructs the entire original integral cubic. -/
theorem completePointOrigin_toProj_isIso : IsIso (toProj (A) hA) := by
  let _ : IsNoetherianRing Γ(Spec (.of (PowerSeries K)), ⊤) :=
    isNoetherianRing_of_ringEquiv (PowerSeries K)
      (Scheme.ΓSpecIso (.of (PowerSeries K))).symm.commRingCatIsoToRingEquiv
  exact ProperAmpleSectionProjIso.isIso (integralCurveStructure (W)) (A)
    (completePointOriginLine_ample K n h i) hA

/-- The original cubic, identified with Proj of its own full origin-line section ring. -/
def completePointOriginProjIso : integralCurve (W) ≅ Proj (grade (A) ⊤) := by
  let _ := completePointOrigin_toProj_isIso K n h i
  exact asIso (toProj (A) hA)

/-- Reconstruction retains the canonical homogeneous-fraction morphism. -/
theorem completePointOriginProjIso_hom :
    (completePointOriginProjIso K n h i).hom = toProj (A) hA := rfl

/-- The reconstructed cubic's homogeneous coordinate opens are its original affine charts. -/
theorem completePointOriginProjIso_preimage (j : Fin 3) :
    (completePointOriginProjIso K n h i).hom ⁻¹ᵁ
      Proj.basicOpen (grade (A) ⊤) (of (A) ⊤ 3 (completePointCubicSections K n h i j)) =
        (integralCurveChart (W) j).opensRange := by
  rw [completePointOriginProjIso_hom, SectionGradedProjOpens.toProj_preimage_basicOpen
    (A) hA _ (by decide), completePointCubicSections_generatorOpen]

/-- The canonical reconstruction commutes with the original complete coefficient base. -/
@[reassoc] theorem completePointOriginProjIso_toBase :
    (completePointOriginProjIso K n h i).hom ≫
      SectionGradedProjStructuralMap.toBase (integralCurveStructure (W)) (A) =
        integralCurveStructure (W) :=
  SectionGradedProjStructuralMap.toProj_toBase (integralCurveStructure (W)) (A) hA

end FLT.Mazur.PolygonInfinitesimalStages
