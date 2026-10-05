/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBaseSectionAlgebra
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# The section-algebra functor over an affine base

Global sections give a contravariant functor from schemes over `Spec A` to
`A`-algebras. On affine objects its spectrum recovers the source, naturally
in all base-compatible arrows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable (A : Type u) [CommRing A]

/-- The actual section algebra of a scheme over `Spec A`. -/
def affineBaseSections (X : Over (Spec (.of A))) : CommAlgCat A :=
  letI := affineBaseSectionAlgebra X.hom
  .of A Γ(X.left, ⊤)

/-- The contravariant section-algebra functor over the fixed affine base. -/
def affineBaseSectionFunctor : (Over (Spec (.of A)))ᵒᵖ ⥤ CommAlgCat A where
  obj X := affineBaseSections A X.unop
  map {X Y} f := by
    letI := affineBaseSectionAlgebra X.unop.hom
    letI := affineBaseSectionAlgebra Y.unop.hom
    exact CommAlgCat.ofHom (affineBaseSectionHom _ _ f.unop.left f.unop.w)
  map_id X := by
    apply CommAlgCat.Hom.ext
    exact affineBaseSectionHom_id X.unop.hom
  map_comp f g := by
    apply CommAlgCat.Hom.ext
    exact affineBaseSectionHom_comp _ _ _ g.unop.left f.unop.left g.unop.w f.unop.w

/-- A morphism's underlying ring map is the ordinary pullback of global sections. -/
theorem affineBaseSectionFunctor_map_ringHom
    {X Y : (Over (Spec (.of A)))ᵒᵖ} (f : X ⟶ Y) :
    ((affineBaseSectionFunctor A).map f).hom.toRingHom = f.unop.left.appTop.hom := rfl

/-- Recover an affine scheme from its actual section algebra. -/
def affineBaseSectionsSpecIso (X : Over (Spec (.of A))) [IsAffine X.left] :
    X.left ≅ Spec ((forget₂ (CommAlgCat A) CommRingCat).obj (affineBaseSections A X)) :=
  X.left.isoSpec

/-- The recovery isomorphisms retain the specified scheme arrows. -/
@[reassoc]
theorem affineBaseSectionsSpecIso_naturality {X Y : Over (Spec (.of A))}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    (affineBaseSectionsSpecIso A X).hom ≫
        Spec.map (CommRingCat.ofHom (((affineBaseSectionFunctor A).map f.op).hom.toRingHom)) =
      f.left ≫ (affineBaseSectionsSpecIso A Y).hom :=
  Scheme.isoSpec_hom_naturality f.left

/-- The spectrum identification retains the given structural morphism to the base. -/
@[reassoc]
theorem affineBaseSectionsSpecIso_over (X : Over (Spec (.of A))) [IsAffine X.left] :
    (affineBaseSectionsSpecIso A X).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (affineBaseSections A X))) = X.hom := by
  change X.left.isoSpec.hom ≫
    Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ X.hom.appTop) = X.hom
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp [Scheme.isoSpec_Spec_hom]

/-- The finite presentation of these algebras is supplied by the structural morphism. -/
theorem affineBaseSections_finitePresentation (X : Over (Spec (.of A)))
    [IsAffine X.left] [LocallyOfFinitePresentation X.hom] :
    Algebra.FinitePresentation A (affineBaseSections A X) :=
  affineBaseSection_finitePresentation X.hom

end FLT.Mazur.Approximation
