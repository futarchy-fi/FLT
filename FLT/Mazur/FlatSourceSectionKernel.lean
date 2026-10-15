/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassFlatSectionRegular

/-!
# Scalar saturation of section kernels with a flat source

Regular base scalars stay regular on sections of every source open. Hence
the section kernel of a map whose source is flat over the base is saturated
with respect to those scalars, even when the inverse-image open is not affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FlatSourceSectionKernel
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y S : Scheme} [IsAffine S]

/-- Regular affine-base scalars stay regular on sections of an arbitrary source open. -/
theorem open_scalar_regular (f : X ⟶ S) [Flat f] (U : X.Opens)
    (a : Γ(S, ⊤)) (ha : IsRegular a) :
    IsRegular (f.appLE ⊤ U (by simp) a) := by
  have hl : IsLeftRegular (f.appLE ⊤ U (by simp) a) := by
    intro b c h
    apply TopCat.Presheaf.section_ext X.sheaf U b c
    intro x hx
    change X.presheaf.germ U x hx b = X.presheaf.germ U x hx c
    have hr := flatRingHom_isRegular (f.stalkMap x).hom (Flat.stalkMap f x)
      (affineGerm_isRegular ha (f x))
    have he : f.stalkMap x (S.presheaf.Γgerm (f x) a) =
        X.presheaf.germ U x hx (f.appLE ⊤ U (by simp) a) := by
      simp [TopCat.Presheaf.Γgerm, Scheme.Hom.appLE]
    rw [he] at hr
    apply hr.left
    simpa only [map_mul] using congrArg (X.presheaf.germ U x hx) h
  exact ⟨hl, fun b c h ↦ hl (by simpa only [mul_comm] using h)⟩

/-- A regular base factor may be cancelled in the original section kernel. -/
theorem cancel_base_scalar (f : X ⟶ Y) (s : Y ⟶ S) [Flat (f ≫ s)]
    (V : Y.Opens) (a : Γ(S, ⊤)) (ha : IsRegular a) (z : Γ(Y, V))
    (hz : f.app V (s.appLE ⊤ V (by simp) a * z) = 0) : f.app V z = 0 := by
  have hr := open_scalar_regular (f ≫ s) (f ⁻¹ᵁ V) a ha
  have he : f.app V (s.appLE ⊤ V (by simp) a) =
      (f ≫ s).appLE ⊤ (f ⁻¹ᵁ V) (by simp) a := by
    rw [f.app_eq_appLE]
    change (s.appLE ⊤ V (by simp) ≫ f.appLE V (f ⁻¹ᵁ V) le_rfl) a = _
    rw [Scheme.Hom.appLE_comp_appLE]
  apply hr.left
  simpa only [map_mul, he, mul_zero] using hz

end FLT.Mazur.FlatSourceSectionKernel
