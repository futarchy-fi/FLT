/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSpecSections
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Regular elements pulled back to sections of a flat scheme

Stalkwise flatness suffices to preserve a regular element of an affine target.
The source need not be affine, and its global sections need not be flat.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A flat ring map preserves regular elements. -/
theorem flatRingHom_isRegular {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) {a : A} (ha : IsRegular a) : IsRegular (f a) := by
  let _ := f.toAlgebra
  let _ : Module.Flat A B := hf
  have h := Module.Flat.isSMulRegular_of_isRegular (M := B) ha
  have hl : IsLeftRegular (f a) := by
    simpa only [IsLeftRegular, IsSMulRegular, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra] using h
  exact ⟨hl, fun x y he => hl (by simpa only [mul_comm] using he)⟩

/-- The germ of a regular section of an affine scheme is regular. -/
theorem affineGerm_isRegular {Y : Scheme} [IsAffine Y]
    {a : Γ(Y, ⊤)} (ha : IsRegular a) (y : Y) :
    IsRegular (Y.presheaf.Γgerm y a) := by
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf
    (⟨y, trivial⟩ : (⊤ : Y.Opens))
  let _ := (isAffineOpen_top Y).isLocalization_stalk ⟨y, trivial⟩
  exact flatRingHom_isRegular _ (RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Y.presheaf.stalk y)
      ((isAffineOpen_top Y).primeIdealOf ⟨y, trivial⟩).asIdeal.primeCompl)) ha

/-- Pulling back a regular global section from an affine target preserves regularity. -/
theorem flat_appTop_isRegular {X Y : Scheme} [IsAffine Y]
    (f : X ⟶ Y) [Flat f] {a : Γ(Y, ⊤)} (ha : IsRegular a) :
    IsRegular (f.appTop a) := by
  have hl : IsLeftRegular (f.appTop a) := by
    intro b c h
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ b c
    intro x hx
    change X.presheaf.germ ⊤ x hx b = X.presheaf.germ ⊤ x hx c
    have hr := flatRingHom_isRegular (f.stalkMap x).hom (Flat.stalkMap f x)
      (affineGerm_isRegular ha (f x))
    have he : f.stalkMap x (Y.presheaf.Γgerm (f x) a) =
        X.presheaf.germ ⊤ x hx (f.appTop a) := by
      simp [TopCat.Presheaf.Γgerm, Scheme.Hom.appTop]
    rw [he] at hr
    apply hr.left
    simpa only [map_mul] using congrArg (X.presheaf.germ ⊤ x hx) h
  exact ⟨hl, fun b c h => hl (by simpa only [mul_comm] using h)⟩

/-- An affine-chart specialization along a flat map preserves regular elements. -/
theorem specSectionHom_isRegular {X : Scheme} {A : Type*} [CommRing A]
    (f : X ⟶ Spec (.of A)) [Flat f] {a : A} (ha : IsRegular a) :
    IsRegular (specSectionHom f a) := by
  apply flat_appTop_isRegular f
  exact flatRingHom_isRegular (Scheme.ΓSpecIso (.of A)).inv.hom
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) ha

end FLT.Mazur.WeierstrassIntegralChart
