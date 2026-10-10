/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedSubringZeroRing
public import FLT.Mazur.SectionRetainedProjConstruction

/-!
# The original structural map of the retained Proj

The unchanged degree-zero ring provides the retained Proj with its original
structural base map. The canonical morphism commutes with that base map,
using the original degree-zero section evaluation on every local chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedProjStructuralMap

open FCurve SectionGradedSum SectionRetainedProjConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- Original structure-sheaf scalars insert into the retained internal degree-zero ring. -/
def zeroScalars : Γ(X, ⊤) →+* RetainedSubringGrading.grade (grade L ⊤) q 0 :=
  (RetainedSubringZeroRing.ringEquiv (grade L ⊤) q).symm.toRingHom.comp
    (algebraMap Γ(X, ⊤) (grade L ⊤ 0))

/-- The retained Proj maps to the spectrum of the original global functions. -/
def toSpecFunctions : Proj (RetainedSubringGrading.grade (grade L ⊤) q) ⟶ Spec Γ(X, ⊤) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (zeroScalars L q))

/-- Evaluating a retained degree-zero scalar gives the original pullback of that function. -/
theorem evaluation_zero {Y : Scheme} (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (SectionRetainedProjChart.ringHom p L e q f)) (r : Γ(X, ⊤)) :
    GradedProjUnitChart.evaluation _ (SectionRetainedProjChart.ringHom p L e q) f hf
      (fromZeroRingHom _ _ (zeroScalars L q r)) = p.appTop r := by
  have he := GradedProjUnitChart.evaluation_mk_mul _
    (SectionRetainedProjChart.ringHom p L e q) f hf
    ⟨0, zeroScalars L q r, 1, one_mem _⟩
  change GradedProjUnitChart.evaluation _ (SectionRetainedProjChart.ringHom p L e q) f hf
      (fromZeroRingHom _ _ (zeroScalars L q r)) *
      SectionRetainedProjChart.ringHom p L e q 1 =
      SectionRetainedProjChart.ringHom p L e q (zeroScalars L q r).val at he
  rw [map_one, mul_one] at he
  refine he.trans ?_
  change SectionGradedProjChart.ringHom p L e (of L ⊤ 0 r) = p.appTop r
  rw [SectionGradedProjChart.ringHom_of, SectionGradedPullback.pull_zero]
  rfl

/-- Every local retained chart commutes with the spectrum of original functions. -/
@[reassoc]
theorem chart_toSpecFunctions {Y : Scheme} (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (SectionRetainedProjChart.ringHom p L e q f))
    {d : ℕ} (hd : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hpos : 0 < d) :
    SectionRetainedProjChart.toProj p L e q f hf hd hpos ≫ toSpecFunctions L q =
      p ≫ X.toSpecΓ := by
  have he : ((GradedProjUnitChart.evaluation _
      (SectionRetainedProjChart.ringHom p L e q) f hf).comp
      (fromZeroRingHom _ _)).comp (zeroScalars L q) = p.appTop.hom := by
    ext r
    exact evaluation_zero L q p e f hf r
  unfold SectionRetainedProjChart.toProj GradedProjUnitChart.toProj toSpecFunctions
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc]
  simp only [GradedProjUnitChart.toAffine, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [← RingHom.comp_assoc, he]
  exact (Scheme.toSpecΓ_naturality p).symm

/-- The canonical retained Proj map preserves the original global functions. -/
@[reassoc]
theorem toProj_toSpecFunctions (h : PositivePowerGenerated L q) :
    toProj L q h ≫ toSpecFunctions L q = X.toSpecΓ := by
  obtain ⟨𝒰, e, d, s, hd, hs⟩ := exists_generating_cover L q h
  apply 𝒰.hom_ext
  intro i
  rw [← Category.assoc, toProj_comp L q h (𝒰.f i) (e i) (s i) (hd i) (hs i)]
  exact chart_toSpecFunctions L q (𝒰.f i) (e i) _ _ _ _

/-- The retained structural morphism to any original affine base. -/
def toBase (f : X ⟶ S) [IsAffine S] :
    Proj (RetainedSubringGrading.grade (grade L ⊤) q) ⟶ S :=
  toSpecFunctions L q ≫ Spec.map f.appTop ≫ inv S.toSpecΓ

/-- Over an affine base the retained canonical morphism has the actual original structure map. -/
@[reassoc]
theorem toProj_toBase (f : X ⟶ S) [IsAffine S] (h : PositivePowerGenerated L q) :
    toProj L q h ≫ toBase L q f = f := by
  rw [toBase, ← Category.assoc, toProj_toSpecFunctions, ← Scheme.toSpecΓ_naturality_assoc,
    IsIso.hom_inv_id, Category.comp_id]

end FLT.Mazur.SectionRetainedProjStructuralMap
