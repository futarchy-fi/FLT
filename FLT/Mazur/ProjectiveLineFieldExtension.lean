/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineProductOverlap
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# ProjectiveLineFieldExtension

The actual pulled-back projective line is identified with the specified
line over the extension field, retaining its structure map and endpoints.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.ProjectiveLineFieldExtension
open ProjectiveLineProductCharts
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The pulled-back projective line is the specified line over the extension. -/
def equivalence : product K L ≅ ProjectiveLine.scheme L :=
  (ProjectiveLineProductOverlap.isPushout K L).isoPushout

@[reassoc (attr := simp)] theorem left_inv :
    ProjectiveLine.left L ≫ (equivalence K L).inv = productChartMap K L false :=
  (ProjectiveLineProductOverlap.isPushout K L).inl_isoPushout_inv
@[reassoc (attr := simp)] theorem right_inv :
    ProjectiveLine.right L ≫ (equivalence K L).inv = productChartMap K L true :=
  (ProjectiveLineProductOverlap.isPushout K L).inr_isoPushout_inv

@[reassoc (attr := simp)] theorem inv_base :
    (equivalence K L).inv ≫ pullback.fst _ _ = ProjectiveLine.toBase L := by
  apply pushout.hom_ext
  · change ProjectiveLine.left L ≫ _ = ProjectiveLine.left L ≫ _
    rw [left_inv_assoc, productChartMap_fst, ProjectiveLine.left_toBase]
    rfl
  · change ProjectiveLine.right L ≫ _ = ProjectiveLine.right L ≫ _
    rw [right_inv_assoc, productChartMap_fst, ProjectiveLine.right_toBase]
    rfl

/-- The projective-line comparison retains the structure morphism to the new field. -/
def componentIso : PolygonPinching.component L ≅
    (Over.pullback (parameterToBase K L)).obj (PolygonPinching.component K) :=
  Over.isoMk ((equivalence K L).symm ≪≫ pullbackSymmetry _ _)
    (by simp)

/-- The base point is preserved by extension of the coefficient field. -/
def pointIso : PolygonPinching.point L ≅
    (Over.pullback (parameterToBase K L)).obj (PolygonPinching.point K) :=
  Over.isoMk (asIso (pullback.snd (𝟙 _) (parameterToBase K L))).symm (by simp)

@[reassoc (attr := simp)] theorem point_fst :
    (pointIso K L).hom.left ≫ pullback.fst (𝟙 (Spec (.of K)))
      (parameterToBase K L) = parameterToBase K L := by
  simp [pointIso]

@[reassoc (attr := simp)] theorem point_snd :
    (pointIso K L).hom.left ≫ pullback.snd (𝟙 (Spec (.of K)))
      (parameterToBase K L) = 𝟙 _ := by
  simp [pointIso]

theorem chartZero_coeff : ProjectiveLine.chartZero L ≫
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K L))) =
      parameterToBase K L ≫ ProjectiveLine.chartZero K := by
  simp only [ProjectiveLine.chartZero, parameterToBase, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext <;> simp

@[reassoc] theorem zero_component :
    ProjectiveLine.zeroSection L ≫ (componentIso K L).hom =
      (pointIso K L).hom ≫ (Over.pullback (parameterToBase K L)).map
        (ProjectiveLine.zeroSection K) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · dsimp only [PolygonPinching.component]
    simp only [Over.comp_left, componentIso, Over.isoMk_hom_left, Iso.trans_hom,
      Iso.symm_hom, Category.assoc,
      Over.pullback_map_left, pullback.lift_fst, Over.mk_hom, point_fst_assoc]
    erw [pullbackSymmetry_hom_comp_fst]
    change ProjectiveLine.zero L ≫ (equivalence K L).inv ≫ pullback.snd _ _ = _
    rw [ProjectiveLine.zero, Category.assoc, left_inv_assoc, productChartMap_snd]
    rw [← Category.assoc, chartZero_coeff]
    rfl
  · exact (ProjectiveLine.zeroSection L ≫ (componentIso K L).hom).w.trans
      ((pointIso K L).hom ≫ (Over.pullback (parameterToBase K L)).map
        (ProjectiveLine.zeroSection K)).w.symm

@[reassoc] theorem infinity_component :
    ProjectiveLine.infinitySection L ≫ (componentIso K L).hom =
      (pointIso K L).hom ≫ (Over.pullback (parameterToBase K L)).map
        (ProjectiveLine.infinitySection K) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · dsimp only [PolygonPinching.component]
    simp only [Over.comp_left, componentIso, Over.isoMk_hom_left, Iso.trans_hom,
      Iso.symm_hom, Category.assoc,
      Over.pullback_map_left, pullback.lift_fst, Over.mk_hom, point_fst_assoc]
    erw [pullbackSymmetry_hom_comp_fst]
    change ProjectiveLine.infinity L ≫ (equivalence K L).inv ≫ pullback.snd _ _ = _
    rw [ProjectiveLine.infinity, Category.assoc, right_inv_assoc, productChartMap_snd]
    rw [← Category.assoc, chartZero_coeff]
    rfl
  · exact (ProjectiveLine.infinitySection L ≫ (componentIso K L).hom).w.trans
      ((pointIso K L).hom ≫ (Over.pullback (parameterToBase K L)).map
        (ProjectiveLine.infinitySection K)).w.symm
end FLT.Mazur.ProjectiveLineFieldExtension
