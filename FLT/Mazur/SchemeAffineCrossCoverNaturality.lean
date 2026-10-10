/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementComparison

/-!
# Naturality of cross-cover comparisons

Faithfully flat reconstruction transfers naturality of the original descent
transport to the effective comparison of two independently chosen covering maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M N : Y.Modules}
variable (D : Data p M) (E : Data p N)
variable (a : Spec R ⟶ X) (b c : Spec S ⟶ Y)
variable (wb : Spec.map φ ≫ a = b ≫ p) (wc : Spec.map φ ≫ a = c ≫ p)
variable (hφ : φ.hom.FaithfullyFlat)
variable [((pullback b).obj M).IsQuasicoherent] [((pullback c).obj M).IsQuasicoherent]
variable [((pullback b).obj N).IsQuasicoherent] [((pullback c).obj N).IsQuasicoherent]
attribute [local irreducible] chartSheaf chartCrossCoverIso chartMap chartReconstruction

/-- Effective cross-cover comparisons commute with compatible original module maps. -/
@[reassoc]
theorem chartCrossCoverIso_naturality (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    D.chartMap φ p E a b wb hφ f hf ≫ (E.chartCrossCoverIso φ p a b c wb wc hφ).hom =
      (D.chartCrossCoverIso φ p a b c wb wc hφ).hom ≫
        D.chartMap φ p E a c wc hφ f hf := by
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique φ hφ
    (E.chartReconstruction φ p a c wc hφ)
  simp only [Functor.map_comp, Category.assoc, chartCrossCoverIso_reconstruction,
    chartMap_reconstruction, chartMap_reconstruction_assoc,
    chartCrossCoverIso_reconstruction_assoc]
  rw [D.transport_naturality E f hf]


end FLT.Mazur.SchemeGeometricDescent.Data
