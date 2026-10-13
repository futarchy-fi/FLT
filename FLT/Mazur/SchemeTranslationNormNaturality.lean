/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeTranslationNormTests

/-!
# Naturality of regular translation norms on arbitrary schemes

The glued finite-free norm commutes with every source morphism. Neither source
nor target is required to be affine, and the covers may be chosen independently.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation
universe u v w w'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (Y Z V : Over (Spec (.of R))) [IsAffine V.left]
/-- Preserve the original translation algebra in the global naturality statement. -/
local instance naturalityTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((prod Y V).left, ⊤)) (h : Z ⟶ Y)

/-- Pulling back an actual envelope section agrees with changing the affine test. -/
theorem localNorm_pullback {T : Over (Spec (.of R))} [IsAffine T.left] (t : T ⟶ Z) :
    localNorm Z V b ((prod.map h (𝟙 V)).left.appTop s) t =
      localNorm Y V b s (t ≫ h) := by
  have he : prod.map (t ≫ h) (𝟙 V) = prod.map t (𝟙 V) ≫ prod.map h (𝟙 V) := by
    apply prod.hom_ext <;> simp only [Category.assoc, prod.map_fst,
      prod.map_snd, Category.comp_id, prod.map_fst_assoc]
  dsimp only [localNorm]
  rw [he, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

/-- Global regular norms commute with every source morphism and independently chosen covers. -/
theorem norm_natural (C : Y.left.OpenCover.{w}) [∀ i, IsAffine (C.X i)]
    (D : Z.left.OpenCover.{w'}) [∀ i, IsAffine (D.X i)] :
    h.left.appTop (norm Y V b s C) =
      norm Z V b ((prod.map h (𝟙 V)).left.appTop s) D := by
  apply norm_unique Z V b _ D
  intro i
  have ht := norm_test Y V b s C (coverArrow Z D i ≫ h)
  rw [localNorm_pullback]
  exact ht

/-- A cover-independent choice of the genuine global regular norm. -/
def regularNorm : Γ(Y.left, ⊤) := norm Y V b s Y.left.affineCover

/-- The intrinsic choice agrees with the norm constructed from every affine cover. -/
theorem regularNorm_eq (C : Y.left.OpenCover.{w}) [∀ i, IsAffine (C.X i)] :
    regularNorm Y V b s = norm Y V b s C :=
  norm_cover_independent Y V b s Y.left.affineCover C

/-- The intrinsic regular norm is natural on arbitrary source schemes. -/
theorem regularNorm_natural :
    h.left.appTop (regularNorm Y V b s) =
      regularNorm Z V b ((prod.map h (𝟙 V)).left.appTop s) :=
  norm_natural Y Z V b s h Y.left.affineCover Z.left.affineCover

end FLT.Mazur.SchemeTranslationNorm
