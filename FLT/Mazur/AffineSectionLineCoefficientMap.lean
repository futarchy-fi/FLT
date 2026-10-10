/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLinePoint
public import FLT.Mazur.ProjectiveSpaceCoefficientMap

/-!
# Changing the coefficient base of an actual affine section-line point

Composing with the projective coefficient morphism changes the structural
ring map and preserves the original test-scheme section submodule.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {ι : Type u}

/-- A unit-coordinate point respects the original projective coefficient morphism. -/
lemma unitChartPoint_coefficientMap (φ : R →+* S) (ψ : S →+* T)
    (v : ι → T) (i : ι) (a : Tˣ) (hi : v i = a) :
    unitChartPoint S ι ψ v i a hi ≫ coefficientMap φ ι =
      unitChartPoint R ι (ψ.comp φ) v i a hi := by
  rw [unitChartPoint, Category.assoc, chartMap_coefficientMap, ← Category.assoc,
    ← Spec.map_comp]
  have h : (unitChartEval S ι ψ v i a hi).comp (coefficientChartRingMap φ ι i) =
      unitChartEval R ι (ψ.comp φ) v i a hi := by
    apply chartRing_hom_ext R ι i
    · intro r
      simp only [RingHom.comp_apply, coefficientChartRingMap_scalar, unitChartEval_scalar]
    · intro j
      simp only [RingHom.comp_apply, coefficientChartRingMap_coordinate,
        unitChartEval_coordinate]
  change Spec.map (CommRingCat.ofHom
    ((unitChartEval S ι ψ v i a hi).comp (coefficientChartRingMap φ ι i))) ≫ _ = _
  rw [h]
  rfl

/-- Changing the base ring leaves the actual section submodule untouched. -/
lemma sectionLinePoint_coefficientMap (φ : R →+* S) (ψ : S →+* T)
    (i : ι) (L : NormalizedSectionLine.Chart T ι i) :
    sectionLinePoint S ι ψ i L ≫ coefficientMap φ ι =
      sectionLinePoint R ι (ψ.comp φ) i L := by
  rw [sectionLinePoint_eq_unitChartPoint, unitChartPoint_coefficientMap,
    sectionLinePoint_eq_unitChartPoint]

variable {X : Scheme.{u}} [IsAffine X]

/-- The coefficient law holds on the original affine test scheme. -/
lemma affineSectionLinePoint_coefficientMap (φ : R →+* S) (ψ : S →+* Γ(X, ⊤))
    (i : ι) (L : NormalizedSectionLine.Chart Γ(X, ⊤) ι i) :
    affineSectionLinePoint ψ i L ≫ coefficientMap φ ι =
      affineSectionLinePoint (ψ.comp φ) i L := by
  rw [affineSectionLinePoint, Category.assoc, sectionLinePoint_coefficientMap]
  rfl

/-- Actual vector image points retain their vectors after changing the coefficient base. -/
lemma affineGeneratorPoint_coefficientMap (φ : R →+* S) (ψ : S →+* Γ(X, ⊤))
    (v : ι → Γ(X, ⊤)) (i : ι) (a : Γ(X, ⊤)ˣ) (hi : v i = a) :
    affineGeneratorPoint ψ v i a hi ≫ coefficientMap φ ι =
      affineGeneratorPoint (ψ.comp φ) v i a hi :=
  affineSectionLinePoint_coefficientMap φ ψ i _

end FLT.Mazur.ProjectiveSpace
