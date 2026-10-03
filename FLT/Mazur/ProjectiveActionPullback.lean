/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupFieldExtension
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Universal projective-line action under the actual pullback functor

The product comparison has exactly the two coefficient-change projections.
Universal scaling naturality therefore identifies the pulled-back action
with scaling in the extension-field projective-line coordinates.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.ProjectiveActionPullback
open ProjectiveLineProductCharts ProjectiveActionFieldExtension PolygonPinching
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
local notation "F" => Over.pullback (parameterToBase K L)
local notation "eG" => MultiplicativeGroupFieldExtension.equivalence K L
local notation "eP" => ProjectiveLineFieldExtension.componentIso K L

@[reassoc] theorem component_fst :
    (eP).hom.left ≫ pullback.fst (component K).hom (parameterToBase K L) = coeff K L := by
  change (ProjectiveLineFieldExtension.equivalence K L).inv ≫
    (pullbackSymmetry _ _).hom ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_hom_comp_fst]
  rfl

@[reassoc] theorem product_fst :
    (((eG).hom ⊗ₘ (eP).hom) ≫ Functor.LaxMonoidal.μ (F) _ _).left ≫
      pullback.fst (MultiplicativeGroupScheme.gm K ⊗ component K).hom
        (parameterToBase K L) = productCoeff K L := by
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_fst]
    erw [Over.tensorHom_left_fst_assoc]
    rw [MultiplicativeGroupFieldExtension.hom_fst]
    change pullback.fst (parameterToBase L (ProjectiveLineUniversalAction.parameter L)) _ ≫
      gmCoeff K L = productCoeff K L ≫
        pullback.fst (parameterToBase K (ProjectiveLineUniversalAction.parameter K)) _
    simp [productCoeff, pullback.map]
  · simp only [Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_snd]
    erw [Over.tensorHom_left_snd_assoc]
    rw [component_fst]
    change pullback.snd (parameterToBase L (ProjectiveLineUniversalAction.parameter L)) _ ≫
      coeff K L = productCoeff K L ≫
        pullback.snd (parameterToBase K (ProjectiveLineUniversalAction.parameter K)) _
    simp [productCoeff, pullback.map]

/-- Under the actual two pullback isomorphisms, universal scaling is the pulled-back action. -/
theorem action :
    ((eG).hom ⊗ₘ (eP).hom) ≫ Functor.LaxMonoidal.μ (F) _ _ ≫
      (F).map (ProjectiveLineUniversalAction.act K) =
    ProjectiveLineUniversalAction.act L ≫ (eP).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, ← Over.comp_left, product_fst_assoc,
      component_fst]
    exact action_natural K L
  · exact (((eG).hom ⊗ₘ (eP).hom) ≫ Functor.LaxMonoidal.μ (F) _ _ ≫
      (F).map (ProjectiveLineUniversalAction.act K)).w.trans
        (ProjectiveLineUniversalAction.act L ≫ (eP).hom).w.symm
end FLT.Mazur.ProjectiveActionPullback
