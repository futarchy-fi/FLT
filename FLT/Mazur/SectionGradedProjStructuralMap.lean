/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjStructuralMap
public import FLT.Mazur.SectionGradedProjConstruction
public import FLT.Mazur.SectionGradedBaseChangeGrading

/-!
# The structural map of the section-ring Proj

The canonical map from a positively generated line bundle to its section-ring
Proj is a map over the affine structural base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjStructuralMap
open FCurve SectionGradedSum SectionGradedBaseChange
open SectionGradedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)
  [Fact (LocallyFreeRankOne L)]

/-- The section-ring Proj maps to the spectrum of the structural base's sections. -/
def toSpecBase : Proj (grade L ⊤) ⟶ Spec Γ(S, ⊤) :=
  GradedProjStructuralMap.toSpecBase (grade L ⊤) ≫ Spec.map f.appTop

/-- For an affine base the structural map lands in the base scheme itself. -/
def toBase [IsAffine S] : Proj (grade L ⊤) ⟶ S :=
  toSpecBase f L ≫ inv S.toSpecΓ

omit [Fact (LocallyFreeRankOne L)] in
/-- Local line coordinates respect the structural scalar action. -/
lemma chart_scalar {Y : Scheme} (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y) :
    (SectionGradedProjChart.ringHom p L e).comp
      (algebraMap Γ(S, ⊤) (sectionModule f L)) = (p ≫ f).appTop.hom := by
  ext r
  change SectionGradedProjChart.ringHom p L e
    (algebraMap Γ(S, ⊤) (sectionModule f L) r) = _
  rw [structural_algebraMap, SectionGradedProjChart.ringHom_of,
    SectionGradedPullback.pull_zero]
  rfl

/-- Each canonical local chart commutes with the structural scalar spectrum map. -/
@[reassoc]
lemma chart_toSpecBase {Y : Scheme} (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    {d : ℕ} (s : Γ(ModuleLineBundleTensorPullback.tensorPower L d, ⊤)) (hd : 0 < d)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ d s))) :
    SectionGradedProjChart.toProj p L e (of L ⊤ d s) hs ⟨s, rfl⟩ hd ≫
      toSpecBase f L = p ≫ f ≫ S.toSpecΓ := by
  have he : (SectionGradedProjChart.ringHom p L e).comp
      (algebraMap Γ(X, ⊤) (SectionGradedSum.Sections L ⊤)) = p.appTop.hom := by
    ext r
    change SectionGradedProjChart.ringHom p L e (of L ⊤ 0 r) = _
    rw [SectionGradedProjChart.ringHom_of, SectionGradedPullback.pull_zero]
    rfl
  unfold toSpecBase SectionGradedProjChart.toProj
  rw [← Category.assoc, GradedProjStructuralMap.unitChart_toSpecBase, he]
  change (Y.toSpecΓ ≫ Spec.map p.appTop) ≫ Spec.map f.appTop = _
  rw [← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.toSpecΓ_naturality]

/-- The global canonical Proj morphism lies over the structural scalar spectrum. -/
@[reassoc]
lemma toProj_toSpecBase (h : PositivePowerGenerated L) :
    toProj L h ≫ toSpecBase f L = f ≫ S.toSpecΓ := by
  obtain ⟨𝒰, e, d, s, hd, hs⟩ := exists_generating_cover L h
  apply 𝒰.hom_ext
  intro i
  rw [← Category.assoc, toProj_comp L h (𝒰.f i) (e i) (s i) (hd i) (hs i)]
  exact chart_toSpecBase f L (𝒰.f i) (e i) (s i) (hd i) (hs i)

/-- Over an affine base, the canonical section-ring Proj map is a morphism over that base. -/
@[reassoc]
lemma toProj_toBase [IsAffine S] (h : PositivePowerGenerated L) :
    toProj L h ≫ toBase f L = f := by
  rw [toBase, ← Category.assoc, toProj_toSpecBase, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

end FLT.Mazur.SectionGradedProjStructuralMap
