/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Section algebras over an affine base

A map to `Spec A` supplies the actual `A`-algebra on global sections.
Morphisms over that base induce algebra maps. For affine sources, local
finite presentation supplies finite algebra presentations of these sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] {X Y Z : Scheme.{u}}

/-- The structural ring map on global sections over an affine base. -/
def affineBaseSectionMap (p : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

/-- The section algebra induced by the given structural map. -/
abbrev affineBaseSectionAlgebra (p : X ⟶ Spec (.of A)) : Algebra A Γ(X, ⊤) :=
  (affineBaseSectionMap p).toAlgebra

/-- Pullback of sections along a morphism over `Spec A` is `A`-linear. -/
def affineBaseSectionHom (p : X ⟶ Spec (.of A)) (q : Y ⟶ Spec (.of A))
    (f : X ⟶ Y) (hf : f ≫ q = p) :
    letI := affineBaseSectionAlgebra p
    letI := affineBaseSectionAlgebra q
    Γ(Y, ⊤) →ₐ[A] Γ(X, ⊤) := by
  letI := affineBaseSectionAlgebra p
  letI := affineBaseSectionAlgebra q
  refine ⟨f.appTop.hom, ?_⟩
  intro a
  change f.appTop.hom (q.appTop.hom _) = p.appTop.hom _
  rw [← hf, Scheme.Hom.comp_appTop]
  rfl

/-- Section pullback preserves identities. -/
@[simp]
theorem affineBaseSectionHom_id (p : X ⟶ Spec (.of A)) :
    let := affineBaseSectionAlgebra p
    affineBaseSectionHom p p (𝟙 X) (Category.id_comp p) = AlgHom.id A _ := by
  let := affineBaseSectionAlgebra p
  ext x
  simp [affineBaseSectionHom]

/-- Section pullback reverses composition. -/
theorem affineBaseSectionHom_comp (p : X ⟶ Spec (.of A))
    (q : Y ⟶ Spec (.of A)) (r : Z ⟶ Spec (.of A))
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f ≫ q = p) (hg : g ≫ r = q) :
    let := affineBaseSectionAlgebra p
    let := affineBaseSectionAlgebra q
    let := affineBaseSectionAlgebra r
    affineBaseSectionHom p r (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      (affineBaseSectionHom p q f hf).comp (affineBaseSectionHom q r g hg) := by
  let := affineBaseSectionAlgebra p
  let := affineBaseSectionAlgebra q
  let := affineBaseSectionAlgebra r
  ext x
  simp [affineBaseSectionHom]

/-- Geometric local finite presentation gives the actual section algebra finite presentation. -/
theorem affineBaseSection_finitePresentation (p : X ⟶ Spec (.of A))
    [IsAffine X] [LocallyOfFinitePresentation p] :
    let := affineBaseSectionAlgebra p
    Algebra.FinitePresentation A Γ(X, ⊤) := by
  change (affineBaseSectionMap p).FinitePresentation
  apply p.finitePresentation_appTop.comp
  apply RingHom.FinitePresentation.of_surjective _
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.surjective
  have h : Function.Injective (Scheme.ΓSpecIso (.of A)).inv.hom :=
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.injective
  change (RingHom.ker (Scheme.ΓSpecIso (.of A)).inv.hom).FG
  rw [(RingHom.injective_iff_ker_eq_bot _).mp h]
  exact Submodule.fg_bot

end FLT.Mazur.Approximation
