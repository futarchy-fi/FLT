/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAllPositiveLaws
public import FLT.Mazur.PolygonCompleteIdentityActionSectionProj

/-!
# The original finite action law in the full marking section Proj

At every finite stage, the prescribed scaling and the original contraction
side action agree in the full graded section Proj of the original marking.
The canonical cubic isomorphism transfers the proved whole-polygon equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SectionGradedSum SectionGradedProjConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "L" => completePointLine K n h (0 : Fin n)
local instance finiteIdentitySectionLineFact : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h 0⟩
local notation "e" => completePointCanonicalCubicIso K n h (0 : Fin n)
local notation "t" => toProj (L) (completePointLine_positivePowerGenerated K n h 0)

/-- The original finite scaling commutes with the full original marking section-Proj action. -/
@[reassoc] theorem completeIdentityFiniteComparison_sectionProj (m : ℕ) :
    completeIdentityFiniteScaling K n h m ≫ (t) =
      completeIdentityFiniteInput K n h 0 m ≫ completeIdentityActionSectionProjTarget K n h 0 := by
  apply (cancel_mono (e).hom).mp
  rw [Category.assoc, completePointCanonicalCubicIso_contraction,
    Category.assoc, completeIdentityActionSectionProjTarget_cubic]
  exact completeIdentityFiniteComparison_all K n h m

end FLT.Mazur.PolygonInfinitesimalStages
