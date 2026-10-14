/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionRingIso
public import FLT.Mazur.FunctionSheafGradedBaseAlgebra

/-!
# The original complete-base section-algebra isomorphism

The cubic structural map is valued in the original complete base via its
canonical affine isomorphism. The algebra comparison retains this actual map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "f" => exactVeroneseProjToBase K n h
local notation "A" => originDivisorLine (W) 1
local notation "L" => completePointLine K n h i

/-- The original cubic structural morphism, with the original complete base as target. -/
def completePointCubicToCompleteBase : integralCurve (W) ⟶ S :=
  integralCurveStructure (W) ≫ (S).isoSpec.inv

/-- The unchanged cubic contraction is a morphism over the original complete base. -/
@[reassoc] theorem completePointToIntegralCubic_toCompleteBase :
    (g) ≫ completePointCubicToCompleteBase K n h i = (f) := by
  rw [completePointCubicToCompleteBase, ← Category.assoc,
    completePointToIntegralCubic_over]
  change ((f) ≫ (S).isoSpec.hom) ≫ (S).isoSpec.inv = (f)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The full section-ring identification is an algebra isomorphism over the unchanged base. -/
def completePointSectionAlgIso :
    sectionModule (completePointCubicToCompleteBase K n h i) (A) ≃ₐ[Γ(S, ⊤)]
      sectionModule (f) (L) := by
  let _ := completePointToIntegralCubic_unitMap_isIso K n h i
  exact FunctionSheafGradedSections.algEquiv (g)
    (completePointOriginLine_rankOne K n h i 1) (completePointOriginLineIso K n h i)
    (completePointCubicToCompleteBase K n h i) (f)
    (completePointToIntegralCubic_toCompleteBase K n h i)

/-- The relative algebra comparison is precisely the proved original graded ring map. -/
theorem completePointSectionAlgIso_apply
    (a : sectionModule (completePointCubicToCompleteBase K n h i) (A)) :
    completePointSectionAlgIso K n h i a = completePointSectionRingIso K n h i a := rfl

/-- All coefficients come from the same original base morphism. -/
theorem completePointSectionAlgIso_scalar (r : Γ(S, ⊤)) :
    completePointSectionAlgIso K n h i
        (algebraMap Γ(S, ⊤) (sectionModule (completePointCubicToCompleteBase K n h i) (A)) r) =
      algebraMap Γ(S, ⊤) (sectionModule (f) (L)) r :=
  (completePointSectionAlgIso K n h i).commutes r

end FLT.Mazur.PolygonInfinitesimalStages
