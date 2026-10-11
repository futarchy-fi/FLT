/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ChowProductOpenGluing
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.PrincipalAffineRefinement

/-!
# Separated lifts detected on a regular principal open

A regular localization is schematically dense, even for a nonreduced ring.
If a separated contraction is unchanged over an original principal open,
two affine-source lifts agree whenever that original function pulls back
to a regular element. No density of geometric points is substituted for
schematic density.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.RegularPrincipalOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- A regular principal localization retains every original function. -/
theorem inclusion_schematicallyDense (d : B) (hd : IsRegular d) :
    IsSchemeTheoreticallyDominant (PrincipalAffineRefinement.inclusion d) := by
  apply SurjectiveDominantEpi.spec_schematic
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers d)).mpr
  rintro ⟨x, ⟨n, rfl⟩⟩
  exact hd.pow n

/-- The actual principal-localization map commutes with the original affine map. -/
@[reassoc] theorem map_inclusion (φ : A →+* B) (a : A) :
    Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.map (S := Localization.Away a)
          (Q := Localization.Away (φ a)) φ a)) ≫ PrincipalAffineRefinement.inclusion a =
      PrincipalAffineRefinement.inclusion (φ a) ≫ Spec.map (CommRingCat.ofHom φ) := by
  simp only [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  change IsLocalization.Away.map (Localization.Away a) (Localization.Away (φ a)) φ a
    (algebraMap A (Localization.Away a) x) = algebraMap B (Localization.Away (φ a)) (φ x)
  simp only [IsLocalization.Away.map, IsLocalization.map_eq]

/-- An unchanged principal open detects all lifts when its pulled-back function is regular. -/
theorem lift_ext {X Y : Scheme.{u}} (c : X ⟶ Y) [IsSeparated c]
    (j : Spec (.of A) ⟶ Y) (a : A)
    (e : Spec (.of (Localization.Away a)) ⟶ X)
    (he : IsPullback (𝟙 _) e (PrincipalAffineRefinement.inclusion a ≫ j) c)
    (φ : A →+* B) (ha : IsRegular (φ a)) (f g : Spec (.of B) ⟶ X)
    (hf : f ≫ c = Spec.map (CommRingCat.ofHom φ) ≫ j)
    (hg : g ≫ c = Spec.map (CommRingCat.ofHom φ) ≫ j) : f = g := by
  let _ := inclusion_schematicallyDense (φ a) ha
  apply Chow.schematicallyDense_ext c (hf.trans hg.symm)
    (PrincipalAffineRefinement.inclusion (φ a))
  let p := Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.map (S := Localization.Away a)
      (Q := Localization.Away (φ a)) φ a))
  have h (k : Spec (.of B) ⟶ X)
      (hk : k ≫ c = Spec.map (CommRingCat.ofHom φ) ≫ j) :
      PrincipalAffineRefinement.inclusion (φ a) ≫ k = p ≫ e := by
    have hp : p ≫ (PrincipalAffineRefinement.inclusion a ≫ j) =
        (PrincipalAffineRefinement.inclusion (φ a) ≫ k) ≫ c := by
      rw [Category.assoc, hk, map_inclusion_assoc]
    have hl : he.lift p _ hp = p := by simpa using he.lift_fst p _ hp
    rw [← hl]
    exact (he.lift_snd p _ hp).symm
  exact (h f hf).trans (h g hg).symm

end FLT.Mazur.RegularPrincipalOpen
