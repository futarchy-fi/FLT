/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeTranslationNormGluing

/-!
# Glued translation norms on arbitrary affine tests

Refine the inverse image of the chosen cover by affine charts. The genuine
local norm equations then identify the pullback to every affine test, and
show that the global regular norm is independent of the chosen cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeEffectiveEpiSections
universe u v w w'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (Y V : Over (Spec (.of R))) [IsAffine V.left]
/-- The actual translation section algebra used on all tests. -/
local instance testsTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((prod Y V).left, ⊤))
  (C : Y.left.OpenCover.{w}) [∀ i, IsAffine (C.X i)]

/-- The glued representing map recovers the original chart map. -/
@[reassoc]
theorem normMap_chart (i : C.I₀) :
    C.f i ≫ normMap Y V b s C = localNormMap Y V b s (coverArrow Y C i) :=
  C.ι_glueMorphisms (coverNormMap Y V b s C) (coverNormMap_compatible Y V b s C) i

/-- The glued norm map restricts correctly to every affine test over the source. -/
@[reassoc]
theorem normMap_test {T : Over (Spec (.of R))} [IsAffine T.left] (t : T ⟶ Y) :
    t.left ≫ normMap Y V b s C = localNormMap Y V b s t := by
  apply (show T.left.OpenCover from C.pullback₁ t.left).hom_ext
  intro i
  apply (pullback t.left (C.f i)).affineCover.hom_ext
  intro j
  let a := (pullback t.left (C.f i)).affineCover.f j
  let Q := Over.mk ((a ≫ pullback.fst t.left (C.f i)) ≫ T.hom)
  let _ : IsAffine Q.left := inferInstanceAs
    (IsAffine ((pullback t.left (C.f i)).affineCover.X j))
  let q : Q ⟶ T := Over.homMk (a ≫ pullback.fst t.left (C.f i)) rfl
  let p : Q ⟶ coverObject Y C i :=
    Over.homMk (a ≫ pullback.snd t.left (C.f i)) (by
      dsimp only [coverObject, Q, Over.mk_left, Over.mk_hom]
      rw [Category.assoc, ← pullback.condition_assoc, Over.w t]
      exact (Category.assoc _ _ _).symm)
  have h : q ≫ t = p ≫ coverArrow Y C i := by
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).trans
      ((congrArg (a ≫ ·) (pullback.condition)).trans (Category.assoc _ _ _).symm)
  change a ≫ pullback.fst t.left (C.f i) ≫ t.left ≫ normMap Y V b s C =
    a ≫ pullback.fst t.left (C.f i) ≫ localNormMap Y V b s t
  rw [pullback.condition_assoc, normMap_chart]
  rw [← Category.assoc, ← Category.assoc]
  change p.left ≫ localNormMap Y V b s (coverArrow Y C i) =
    q.left ≫ localNormMap Y V b s t
  rw [localNormMap_comp, localNormMap_comp, h]

/-- Every affine test computes the actual regular norm by the finite-free determinant. -/
theorem norm_test {T : Over (Spec (.of R))} [IsAffine T.left] (t : T ⟶ Y) :
    t.left.appTop (norm Y V b s C) = localNorm Y V b s t := by
  rw [norm, ← functionEquiv_comp, normMap_test]
  exact (functionEquiv T.left).apply_symm_apply _

/-- The glued global norm is independent of the chosen affine open cover. -/
theorem norm_cover_independent (D : Y.left.OpenCover.{w'}) [∀ i, IsAffine (D.X i)] :
    norm Y V b s C = norm Y V b s D := by
  apply norm_unique Y V b s D
  intro i
  exact norm_test Y V b s C (coverArrow Y D i)

end FLT.Mazur.SchemeTranslationNorm
