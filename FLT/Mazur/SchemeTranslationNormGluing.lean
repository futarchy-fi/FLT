/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeTranslationNormLocal
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing finite-free translation norms on a nonaffine scheme

An actual global section of the product envelope gives compatible affine
norms. Glue their representing morphisms on the entire overlaps, using
further affine refinements there. The result is a global regular function
on the source; neither the source nor its intersections need be affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeEffectiveEpiSections
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (Y V : Over (Spec (.of R))) [IsAffine V.left]
/-- Retain the original translation algebra in the gluing interface. -/
local instance gluingTranslationAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((prod Y V).left, ⊤))
  (C : Y.left.OpenCover.{w}) [∀ i, IsAffine (C.X i)]

/-- A cover chart retains its map to the original ground base. -/
def coverObject (i : C.I₀) : Over (Spec (.of R)) := Over.mk (C.f i ≫ Y.hom)

instance coverObject_affine (i : C.I₀) : IsAffine (coverObject Y C i).left :=
  inferInstanceAs (IsAffine (C.X i))

/-- The cover arrow as a morphism over the original ground base. -/
def coverArrow (i : C.I₀) : coverObject Y C i ⟶ Y := Over.homMk (C.f i)

/-- The local norm represented on a chosen affine chart. -/
def coverNormMap (i : C.I₀) : C.X i ⟶ functionScheme :=
  localNormMap Y V b s (coverArrow Y C i)

/-- Local norms agree on the full overlap, even when that overlap is nonaffine. -/
theorem coverNormMap_compatible (i j : C.I₀) :
    pullback.fst (C.f i) (C.f j) ≫ coverNormMap Y V b s C i =
      pullback.snd (C.f i) (C.f j) ≫ coverNormMap Y V b s C j := by
  apply (pullback (C.f i) (C.f j)).affineCover.hom_ext
  intro a
  let t := (pullback (C.f i) (C.f j)).affineCover.f a
  let Q := Over.mk ((t ≫ pullback.fst (C.f i) (C.f j)) ≫ C.f i ≫ Y.hom)
  let _ : IsAffine Q.left := inferInstanceAs
    (IsAffine ((pullback (C.f i) (C.f j)).affineCover.X a))
  let q₁ : Q ⟶ coverObject Y C i :=
    Over.homMk (t ≫ pullback.fst (C.f i) (C.f j)) (by simp only [Category.assoc]; rfl)
  let q₂ : Q ⟶ coverObject Y C j :=
    Over.homMk (t ≫ pullback.snd (C.f i) (C.f j)) (by
      dsimp only [coverObject, Q, Over.mk_left, Over.mk_hom]
      simp only [Category.assoc, ← pullback.condition_assoc])
  have hq : q₁ ≫ coverArrow Y C i = q₂ ≫ coverArrow Y C j := by
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).trans
      ((congrArg (t ≫ ·) (pullback.condition)).trans (Category.assoc _ _ _).symm)
  rw [← Category.assoc, ← Category.assoc]
  change q₁.left ≫ localNormMap Y V b s (coverArrow Y C i) =
    q₂.left ≫ localNormMap Y V b s (coverArrow Y C j)
  rw [localNormMap_comp, localNormMap_comp, hq]

/-- Glue the actual norm morphisms, rather than assuming compatible global coefficients. -/
def normMap : Y.left ⟶ functionScheme :=
  C.glueMorphisms (coverNormMap Y V b s C) (coverNormMap_compatible Y V b s C)

/-- The constructed global norm on the possibly nonaffine original source. -/
def norm : Γ(Y.left, ⊤) := functionEquiv Y.left (normMap Y V b s C)

/-- Restricting the constructed norm recovers every genuine finite-free chart norm. -/
theorem norm_chart (i : C.I₀) :
    (C.f i).appTop (norm Y V b s C) = localNorm Y V b s (coverArrow Y C i) := by
  rw [norm, ← functionEquiv_comp]
  have h := C.ι_glueMorphisms (coverNormMap Y V b s C)
    (coverNormMap_compatible Y V b s C) i
  change C.f i ≫ normMap Y V b s C = coverNormMap Y V b s C i at h
  rw [h]
  exact (functionEquiv (C.X i)).apply_symm_apply _

/-- The chart equations determine the global regular norm uniquely. -/
theorem norm_unique (r : Γ(Y.left, ⊤))
    (hr : ∀ i, (C.f i).appTop r = localNorm Y V b s (coverArrow Y C i)) :
    r = norm Y V b s C := by
  apply (functionEquiv Y.left).symm.injective
  apply C.hom_ext
  intro i
  apply (functionEquiv (C.X i)).injective
  rw [functionEquiv_comp, functionEquiv_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, hr, norm_chart]

end FLT.Mazur.SchemeTranslationNorm
