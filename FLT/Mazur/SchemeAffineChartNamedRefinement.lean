/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartRefinement

/-!
# Refinement comparisons with independently chosen chart endpoints

Common refinements come with named base and cover maps. Transport the effective
comparison to these maps using their geometric factorization equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (α : R ⟶ R') (β : S ⟶ S')
variable (v : φ ≫ β = α ≫ ψ)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)
variable [((pullback b).obj M).IsQuasicoherent]
variable (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)
variable (a' : Spec R' ⟶ X) (b' : Spec S' ⟶ Y)
variable (ha : Spec.map α ≫ a = a') (hb : Spec.map β ≫ b = b')
variable (w' : Spec.map ψ ≫ a' = b' ≫ p)
variable [((pullback b').obj M).IsQuasicoherent]

/-- Effective comparison with descent on a named common affine chart. -/
def chartRefinementIsoTo :
    (pullback (Spec.map α)).obj (D.chartSheaf φ p a b w hφ) ≅
      D.chartSheaf ψ p a' b' w' hψ := by
  subst a' b'
  exact D.chartRefinementIso φ ψ α β v p a b w hφ hψ

/-- Reconstruct the refinement comparison on the named cover chart. -/
def chartRefinementReconstructionTo :
    (pullback (Spec.map ψ)).obj
        ((pullback (Spec.map α)).obj (D.chartSheaf φ p a b w hφ)) ≅
      (pullback b').obj M :=
  AffineDescentRefinement.reconstruction φ ψ α β v hφ (D.affineChart φ p a b w) ≪≫
      (comparison (Spec.map β) b b' hb).app M

/-- The named chart comparison reconstructs its actual cover factorization. -/
@[reassoc]
theorem chartRefinementIsoTo_reconstruction :
    (pullback (Spec.map ψ)).map
        (D.chartRefinementIsoTo φ ψ α β v p a b w hφ hψ a' b' ha hb w').hom ≫
        (D.chartReconstruction ψ p a' b' w' hψ).hom =
      (D.chartRefinementReconstructionTo φ ψ α β v p a b w hφ b' hb).hom := by
  subst a' b'
  simpa only [chartRefinementIsoTo, chartRefinementReconstructionTo,
    chartRefinementReconstruction, comparison, pullbackCongr, eqToIso_refl,
    Iso.trans_refl] using D.chartRefinementIso_reconstruction φ ψ α β v p a b w hφ hψ

end FLT.Mazur.SchemeGeometricDescent.Data
