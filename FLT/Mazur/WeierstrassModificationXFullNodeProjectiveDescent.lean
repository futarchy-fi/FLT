/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeZeroDescent
public import FLT.Mazur.ProjectiveLineSlopeNormalization

/-!
# Projective component descent at both original start-zero attachments

The exterior uses its actual slope normalization. The second attachment keeps
the translation by the negative tangent and its own localized denominator.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ) (c : K) (hc : c = 0)

/-- The original opposite branch translation sends its origin to the negative tangent. -/
@[reassoc] theorem fullNode_translatedParameter_origin :
    ProjectiveLine.chartZero K ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C (a : K))).toRingHom) =
      Spec.map (CommRingCat.ofHom (aeval (-(a : K)) : K[X] →ₐ[K] K).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext <;> simp

local notation "s₁" => fullNodeNormalizedDenominator (a : K) c
local notation "hs₁" => fullNodeNormalizedDenominator_value (a : K) c a.isUnit
local notation "E₁" => conicZeroAffineIso c hc ≪≫ fullNodeConicParameterIso (a : K) c a.isUnit
local notation "s₂" => fullNodeNormalizedDenominator (-(a : K)) c
local notation "hs₂" => fullNodeNormalizedDenominator_value (-(a : K)) c a.isUnit.neg
local notation "E₂" => conicZeroAffineIso c hc ≪≫
  fullNodeConicParameterIso (-(a : K)) c a.isUnit.neg

/-- The reversed first conic and normalized exterior descend on their whole original node. -/
theorem fullNodeZero_first_projective_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.infinity K ≫ f = ProjectiveLine.zero K ≫ g) :
    ∃! d : Spec (.of (FullNodeOpen (a : K) c)) ⟶ Y,
      (E₁).hom ≫ fullNodeFirstBranch (a : K) c a.isUnit ≫ d =
        ProjectiveLine.right K ≫ f ∧
      fullNodeSecondBranch (a : K) c a.isUnit ≫ d =
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₁) ≫
          ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ g := by
  apply fullNodeZero_exists_unique_desc (a : K) c a.isUnit hc
  rw [NodeLocalDescent.secondOrigin_branchOpen_assoc]
  have hz : (aeval (0 : K) : K[X] →ₐ[K] K).toRingHom = evalRingHom 0 := rfl
  simpa only [ProjectiveLine.infinity, ProjectiveLine.infinitySlopeMark,
    ProjectiveLine.chartZero, hz, Category.assoc] using
    w.trans (ProjectiveLine.slopeNormalization_first_assoc a g).symm

/-- The opposite conic descends with the actual translated, localized exterior branch. -/
theorem fullNodeZero_second_projective_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.zero K ≫ f = ProjectiveLine.infinity K ≫ g) :
    ∃! d : Spec (.of (FullNodeOpen (-(a : K)) c)) ⟶ Y,
      (E₂).hom ≫ fullNodeFirstBranch (-(a : K)) c a.isUnit.neg ≫ d =
        ProjectiveLine.left K ≫ f ∧
      fullNodeSecondBranch (-(a : K)) c a.isUnit.neg ≫ d =
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₂) ≫
          Spec.map (CommRingCat.ofHom (aeval (X - C (a : K))).toRingHom) ≫
            ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ g := by
  apply fullNodeZero_exists_unique_desc (-(a : K)) c a.isUnit.neg hc
  rw [NodeLocalDescent.secondOrigin_branchOpen_assoc, fullNode_translatedParameter_origin_assoc]
  simpa only [ProjectiveLine.zero, ProjectiveLine.infinitySlopeMark, Category.assoc] using
    w.trans (ProjectiveLine.slopeNormalization_second_assoc a g).symm

end FLT.Mazur.WeierstrassModificationX
