/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionRingIso
public import FLT.Mazur.GradedProjRingEquiv
public import FLT.Mazur.SectionGradedCommutativity

/-!
# Proj of the original complete-base marking section ring

The degree-preserving full section-ring equivalence identifies the projective
schemes and every homogeneous basic open through the actual section pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedMultiplication SectionGradedSum
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "A" => originDivisorLine (W) 1
local notation "L" => completePointLine K n h i
local notation "e" => completePointOriginLineIso K n h i

local instance originLineFact : Fact (LocallyFreeRankOne (A)) :=
  ⟨completePointOriginLine_rankOne K n h i 1⟩

local instance markingLineFact : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h i⟩

/-- The actual tensor-graded section rings define isomorphic Proj schemes. -/
def completePointSectionProjIso : Proj (grade (L) ⊤) ≅ Proj (grade (A) ⊤) :=
  GradedProjRingEquiv.iso (grade (A) ⊤) (grade (L) ⊤)
    (completePointSectionRingIso K n h i) (completePointSectionRingIso_mem_grade_iff K n h i)

/-- The Proj identification retains the actual full section-ring pullback on basic opens. -/
theorem completePointSectionProjIso_preimage (a : SectionGradedSum.Sections (A) ⊤) :
    (completePointSectionProjIso K n h i).hom ⁻¹ᵁ Proj.basicOpen (grade (A) ⊤) a =
      Proj.basicOpen (grade (L) ⊤) (completePointSectionRingIso K n h i a) := rfl

/-- A homogeneous chart uses exactly the original pulled section in that same degree. -/
theorem completePointSectionProjIso_preimage_of (m : ℕ) (s : Piece (A) ⊤ m) :
    (completePointSectionProjIso K n h i).hom ⁻¹ᵁ
        Proj.basicOpen (grade (A) ⊤) (of (A) ⊤ m s) =
      Proj.basicOpen (grade (L) ⊤)
        (of (L) ⊤ m (SectionGradedLinePullback.sectionMap (g) (e) m ⊤ s)) := by
  rw [completePointSectionProjIso_preimage, completePointSectionRingIso_of]

/-- The same actual comparison preserves intersections of arbitrary homogeneous charts. -/
theorem completePointSectionProjIso_preimage_overlap
    (a b : SectionGradedSum.Sections (A) ⊤) :
    (completePointSectionProjIso K n h i).hom ⁻¹ᵁ
        (Proj.basicOpen (grade (A) ⊤) a ⊓ Proj.basicOpen (grade (A) ⊤) b) =
      Proj.basicOpen (grade (L) ⊤) (completePointSectionRingIso K n h i a) ⊓
        Proj.basicOpen (grade (L) ⊤) (completePointSectionRingIso K n h i b) := by
  exact congrArg₂ (fun U V ↦ U ⊓ V)
    (completePointSectionProjIso_preimage K n h i a)
    (completePointSectionProjIso_preimage K n h i b)

end FLT.Mazur.PolygonInfinitesimalStages
