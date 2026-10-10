/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientGeneration

/-!
# Coherence detected by the original coefficient sections

A square of coefficient-line comparisons commutes when its original global
coordinate sections commute. The source is the actual iterated pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.GradedProjLine

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The standard equality comparison retains the actual global pullback section. -/
theorem pullbackCongr_globalSection {X Y : Scheme} {f g : X ⟶ Y}
    (hfg : f = g) (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((pullbackCongr hfg).hom.app M).app ⊤ (pullGlobal f M s) = pullGlobal g M s := by
  subst g
  rfl

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- Original coordinate sections determine every map out of the coefficient line itself. -/
theorem coefficientSection_hom_ext (hcover : iSup (chart 𝒜 f) = ⊤)
    {M : (Proj 𝒜).Modules} (a b : line 𝒜 f hf 1 ⟶ M)
    (hs : ∀ i, a.app ⊤ (coefficientSection 𝒜 f hf i) =
      b.app ⊤ (coefficientSection 𝒜 f hf i)) : a = b := by
  let _ := coefficientSection_evaluation_epi 𝒜 f hf hcover
  apply (cancel_epi (ProjectiveSpace.globalEvaluation _ (coefficientSection 𝒜 f hf))).mp
  apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan ι)
  intro i
  change SheafOfModules.ιFree i ≫ _ ≫ a = SheafOfModules.ιFree i ≫ _ ≫ b
  rw [← Category.assoc, ModuleGlobalEvaluationPullback.evaluation_generator,
    ← Category.assoc, ModuleGlobalEvaluationPullback.evaluation_generator]
  apply globalSection_hom_ext
  change a.app ⊤ ((globalSectionHom _ _).app ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
    b.app ⊤ ((globalSectionHom _ _).app ⊤ (1 : Γ(Proj 𝒜, ⊤)))
  rw [globalSectionHom_top]
  exact hs i

/-- Agreement on the original homogeneous coordinates forces the comparison square. -/
theorem coefficientSection_comparison_coherence {X Z : Scheme}
    (p : X ⟶ Proj 𝒜) (q : Z ⟶ Proj 𝒜) (r : X ⟶ Z) (hpq : r ≫ q = p)
    (hcover : iSup (chart 𝒜 f) = ⊤) {M : X.Modules} {N : Z.Modules}
    (a : (pullback p).obj (line 𝒜 f hf 1) ⟶ M)
    (b : (pullback q).obj (line 𝒜 f hf 1) ⟶ N)
    (c : (pullback r).obj N ⟶ M)
    (hs : ∀ i, c.app ⊤ (pullGlobal r N
        (b.app ⊤ (pullGlobal q (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i)))) =
      a.app ⊤ (pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i))) :
    (pullback r).map b ≫ c =
      (pullbackComp r q).hom.app (line 𝒜 f hf 1) ≫
        (pullbackCongr hpq).hom.app (line 𝒜 f hf 1) ≫ a := by
  apply (cancel_epi ((pullbackComp r q).inv.app (line 𝒜 f hf 1))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply coefficientSection_pullback_hom_ext 𝒜 f hf hcover (r ≫ q)
  intro i
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullGlobal_comp]
  erw [pullGlobal_naturality r b, pullbackCongr_globalSection]
  exact hs i

end FLT.Mazur.GradedProjLine
