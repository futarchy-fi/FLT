/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineStandardOverlap
public import FLT.Mazur.ProjectiveLineEndpoints
/-!
# Comparison of the glued and standard projective lines

The explicit polynomial and Laurent comparisons identify the constructed
two-chart projective line with Proj of K[X₀,X₁]. The isomorphism preserves
both affine charts, the structure morphism, and the specified endpoints.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.ProjectiveLine
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The specified glued projective line is the standard polynomial Proj. -/
def standardIso : scheme K ≅ ProjectiveSpace.space K (Fin 2) :=
  (ProjectiveLineStandardOverlap.isPushout K).isoPushout.symm

@[reassoc (attr := simp)] theorem left_standardIso :
    left K ≫ (standardIso K).hom = ProjectiveLineStandardCharts.left K :=
  (ProjectiveLineStandardOverlap.isPushout K).inl_isoPushout_inv

@[reassoc (attr := simp)] theorem right_standardIso :
    right K ≫ (standardIso K).hom = ProjectiveLineStandardCharts.right K :=
  (ProjectiveLineStandardOverlap.isPushout K).inr_isoPushout_inv

@[reassoc (attr := simp)] theorem standardIso_toBase :
    (standardIso K).hom ≫ ProjectiveSpace.baseProjection K (Fin 2) = toBase K := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    rw [left_standardIso_assoc, ProjectiveLineStandardCharts.left_base, left_toBase]
  · change right K ≫ _ = right K ≫ _
    rw [right_standardIso_assoc, ProjectiveLineStandardCharts.right_base, right_toBase]

@[reassoc (attr := simp)] theorem standardIso_inv_toBase :
    (standardIso K).inv ≫ toBase K = ProjectiveSpace.baseProjection K (Fin 2) := by
  rw [← standardIso_toBase, Iso.inv_hom_id_assoc]

/-- The comparison preserves the original coefficient projection. -/
def standardOverIso : Over.mk (toBase K) ≅
    Over.mk (ProjectiveSpace.baseProjection K (Fin 2)) :=
  Over.isoMk (standardIso K) (standardIso_toBase K)

@[reassoc (attr := simp)] theorem zero_standardIso :
    zero K ≫ (standardIso K).hom =
      chartZero K ≫ ProjectiveLineStandardCharts.left K := by
  simp [zero]

@[reassoc (attr := simp)] theorem infinity_standardIso :
    infinity K ≫ (standardIso K).hom =
      chartZero K ≫ ProjectiveLineStandardCharts.right K := by
  simp [infinity]
end FLT.Mazur.ProjectiveLine
