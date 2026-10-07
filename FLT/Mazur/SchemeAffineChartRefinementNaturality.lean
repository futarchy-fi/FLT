/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartNamedRefinement

/-!
# Naturality of effective chart refinement

Maps compatible with the original scheme overlap commute with comparison to a
named common affine chart. Faithfully flat reconstruction proves the square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] AffineGeometricOverlapRefinement.data
attribute [local irreducible] chartRefinementIsoTo
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (α : R ⟶ R') (β : S ⟶ S')
variable (v : φ ≫ β = α ≫ ψ)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M N : Y.Modules}
variable (D : Data p M) (E : Data p N)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)
variable [((pullback b).obj M).IsQuasicoherent] [((pullback b).obj N).IsQuasicoherent]
variable (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)
variable (a' : Spec R' ⟶ X) (b' : Spec S' ⟶ Y)
variable (ha : Spec.map α ≫ a = a') (hb : Spec.map β ≫ b = b')
variable (w' : Spec.map ψ ≫ a' = b' ≫ p)
variable (f : M ⟶ N) (hf : D.MapCompatible p E f)

/-- Restricted reconstruction commutes with every compatible original scheme map. -/
@[reassoc]
theorem chartRefinementReconstructionTo_naturality :
    (pullback (Spec.map ψ)).map
        ((pullback (Spec.map α)).map (D.chartMap φ p E a b w hφ f hf)) ≫
        (E.chartRefinementReconstructionTo φ ψ α β v p a b w hφ b' hb).hom =
      (D.chartRefinementReconstructionTo φ ψ α β v p a b w hφ b' hb).hom ≫
        (pullback b').map f := by
  have h := AffineDescentRefinement.reconstruction_naturality φ ψ α β v hφ
    (D.affineChart φ p a b w) (E.affineChart φ p a b w) ((pullback b).map f)
    (D.affineChart_mapCompatible φ p E a b w f hf)
  have hn := (comparison (Spec.map β) b b' hb).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  dsimp only [AffineDescentRefinement.map, AffineDescentRefinement.sheaf] at h
  dsimp only [chartRefinementReconstructionTo, Iso.trans_hom, Iso.app_hom,
    chartMap, chartSheaf]
  rw [← Category.assoc, h, Category.assoc, hn, Category.assoc]

variable [((pullback b').obj M).IsQuasicoherent] [((pullback b').obj N).IsQuasicoherent]

/-- Effective comparison to a named common chart is natural in compatible scheme maps. -/
@[reassoc]
theorem chartRefinementIsoTo_naturality :
    (pullback (Spec.map α)).map (D.chartMap φ p E a b w hφ f hf) ≫
        (E.chartRefinementIsoTo φ ψ α β v p a b w hφ hψ a' b' ha hb w').hom =
      (D.chartRefinementIsoTo φ ψ α β v p a b w hφ hψ a' b' ha hb w').hom ≫
        D.chartMap ψ p E a' b' w' hψ f hf := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback α
    (D.chartSheaf φ p a b w hφ)
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique ψ hψ
    (E.chartReconstruction ψ p a' b' w' hψ)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc,
    chartRefinementIsoTo_reconstruction, Category.assoc, chartMap_reconstruction,
    ← Category.assoc, chartRefinementIsoTo_reconstruction]
  exact D.chartRefinementReconstructionTo_naturality φ ψ α β v p E a b w hφ b' hb f hf

end FLT.Mazur.SchemeGeometricDescent.Data
