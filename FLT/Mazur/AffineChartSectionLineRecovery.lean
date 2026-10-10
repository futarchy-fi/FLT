/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLinePoint

/-!
# Recovering normalized lines from actual affine chart morphisms

A morphism from an affine scheme into a standard projective chart defines
an actual normalized section submodule. Its projective point is the original
chart morphism, with the original coefficient map retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {ι : Type u}
variable {X : Scheme.{u}} [IsAffine X] (φ : R →+* Γ(X, ⊤)) (i : ι)
variable (q : X ⟶ Spec (.of (chartRing R ι i)))
variable (hq : q ≫ Spec.map (CommRingCat.ofHom (chartScalars R ι i)) =
  X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ))

/-- The original affine chart map, transported to its coefficient spectrum. -/
def affineChartSpectrumPoint : AffineChartPoint R ι φ i :=
  ⟨X.isoSpec.inv ≫ q, by
    rw [Category.assoc, hq, Iso.inv_hom_id_assoc]⟩

/-- The normalized actual section submodule recovered from the original affine chart map. -/
def affineChartSectionLine : NormalizedSectionLine.Chart Γ(X, ⊤) ι i :=
  sectionLineChartEquiv R ι φ i (affineChartSpectrumPoint φ i q hq)

/-- Recovery preserves the actual affine scheme point, not only its coordinate tuple. -/
lemma affineChartSectionLine_point :
    affineSectionLinePoint φ i (affineChartSectionLine φ i q hq) = q ≫ chartMap R ι i := by
  rw [affineSectionLinePoint, affineChartSectionLine, sectionLinePoint_classify]
  change X.isoSpec.hom ≫ ((X.isoSpec.inv ≫ q) ≫ chartMap R ι i) = _
  rw [← Category.assoc, Iso.hom_inv_id_assoc]

include hq in
/-- Any given factorization through the actual standard chart recovers its section line. -/
lemma exists_sectionLine_of_chart (p : X ⟶ space R ι) (hp : q ≫ chartMap R ι i = p) :
    ∃ L : NormalizedSectionLine.Chart Γ(X, ⊤) ι i, affineSectionLinePoint φ i L = p :=
  ⟨affineChartSectionLine φ i q hq, (affineChartSectionLine_point φ i q hq).trans hp⟩

end FLT.Mazur.ProjectiveSpace
