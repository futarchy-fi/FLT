/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginProjIso
public import FLT.Mazur.PolygonCompletePointSectionProjIso
public import FLT.Mazur.SectionGradedProjLineNaturality

/-!
# The unchanged cubic contraction is the canonical full section-Proj map

The intrinsic cubic reconstruction commutes with the original contraction
and the full graded section-ring comparison, preserving the original marking line.
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
local notation "g" => completePointToIntegralCubic K n h i
local notation "A" => originDivisorLine (W) 1
local notation "L" => completePointLine K n h i
local notation "e" => completePointOriginLineIso K n h i
local notation "hA" => completePointOriginLine_positivePowerGenerated K n h i

local instance completePointCanonicalLineFact : Fact (LocallyFreeRankOne (A)) :=
  ⟨completePointOriginLine_rankOne K n h i 1⟩
local instance completePointCanonicalMarkingLineFact : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h i⟩

/-- The actual original marking line is positively generated over the full complete base. -/
theorem completePointLine_positivePowerGenerated : PositivePowerGenerated (L) :=
  SectionGradedProjLineNaturality.positivePowerGenerated_pullback (g) (A) (e) hA

/-- The canonical marking Proj map commutes with the unchanged global cubic contraction. -/
@[reassoc] theorem completePointToIntegralCubic_toOriginProj :
    toProj (L) (completePointLine_positivePowerGenerated K n h i) ≫
      (completePointSectionProjIso K n h i).hom =
        (g) ≫ (completePointOriginProjIso K n h i).hom := by
  let hφ := GradedProjRingEquiv.irrelevant_le_forward (grade (A) ⊤) (grade (L) ⊤)
    (completePointSectionRingIso K n h i) (completePointSectionRingIso_mem_grade_iff K n h i)
  exact SectionGradedProjLineNaturality.toProj_map (g) (A) (e) hA hφ

/-- The full marking section Proj is the original cubic, with its actual canonical map. -/
def completePointCanonicalCubicIso : Proj (grade (L) ⊤) ≅ integralCurve (W) :=
  completePointSectionProjIso K n h i ≪≫ (completePointOriginProjIso K n h i).symm

/-- Under the reconstructed cubic identification, the canonical map is the original morphism. -/
@[reassoc] theorem completePointCanonicalCubicIso_contraction :
    toProj (L) (completePointLine_positivePowerGenerated K n h i) ≫
      (completePointCanonicalCubicIso K n h i).hom = (g) := by
  change (toProj (L) _ ≫
    ((completePointSectionProjIso K n h i).hom ≫
      (completePointOriginProjIso K n h i).inv)) = (g)
  rw [← Category.assoc, completePointToIntegralCubic_toOriginProj, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
