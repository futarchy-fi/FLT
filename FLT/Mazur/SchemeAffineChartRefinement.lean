/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartComposition
public import FLT.Mazur.AffineEffectiveRefinementComparison

/-!
# Effective refinement of affine charts of a scheme descent datum

Pulling back a descended chart gives the sheaf descended directly on the
composite chart. Its reconstruction is the actual restricted reconstruction
followed by the cover pullback composition chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] AffineGeometricOverlapRefinement.data
attribute [local irreducible] AffineDescentRefinement.effectiveComparisonIso
attribute [local irreducible] affineChartCompositionIso
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (α : R ⟶ R') (β : S ⟶ S')
variable (v : φ ≫ β = α ≫ ψ)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)
variable [((pullback b).obj M).IsQuasicoherent]
variable (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)

/-- The reconstruction on the composite chart, with the original cover endpoint. -/
def chartRefinementReconstruction :
    (pullback (Spec.map ψ)).obj
        ((pullback (Spec.map α)).obj (D.chartSheaf φ p a b w hφ)) ≅
      (pullback (Spec.map β ≫ b)).obj M :=
  AffineDescentRefinement.reconstruction φ ψ α β v hφ (D.affineChart φ p a b w) ≪≫
    (pullbackComp (Spec.map β) b).app M

/-- The effective comparison between the restricted and directly descended chart sheaves. -/
def chartRefinementIso :
    (pullback (Spec.map α)).obj (D.chartSheaf φ p a b w hφ) ≅
      D.chartSheaf ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
        (affineChart_composite_square φ ψ α β v p a b w) hψ :=
  AffineDescentRefinement.effectiveComparisonIso φ ψ α β v hφ
    (D.affineChart φ p a b w) hψ ≪≫ D.affineChartCompositionIso φ ψ α β v p a b w hψ

/-- The effective chart comparison has the prescribed geometric reconstruction. -/
@[reassoc]
theorem chartRefinementIso_reconstruction :
    (pullback (Spec.map ψ)).map (D.chartRefinementIso φ ψ α β v p a b w hφ hψ).hom ≫
        (D.chartReconstruction ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
          (affineChart_composite_square φ ψ α β v p a b w) hψ).hom =
      (D.chartRefinementReconstruction φ ψ α β v p a b w hφ).hom := by
  dsimp only [chartRefinementIso, Iso.trans_hom]
  rw [Functor.map_comp, Category.assoc, affineChartCompositionIso_reconstruction,
    ← Category.assoc, AffineDescentRefinement.effectiveComparisonIso_reconstruction]
  rfl

/-- Reconstruction uniquely determines the effective comparison of affine chart sheaves. -/
theorem chartRefinementIso_unique
    (f : (pullback (Spec.map α)).obj (D.chartSheaf φ p a b w hφ) ⟶
      D.chartSheaf ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
        (affineChart_composite_square φ ψ α β v p a b w) hψ)
    (hf : (pullback (Spec.map ψ)).map f ≫
      (D.chartReconstruction ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
        (affineChart_composite_square φ ψ α β v p a b w) hψ).hom =
      (D.chartRefinementReconstruction φ ψ α β v p a b w hφ).hom) :
    f = (D.chartRefinementIso φ ψ α β v p a b w hφ hψ).hom := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback α
    (D.chartSheaf φ p a b w hφ)
  exact AffineQuasicoherentPullbackFaithful.reconstruction_unique ψ hψ
    (D.chartReconstruction ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
      (affineChart_composite_square φ ψ α β v p a b w) hψ) f _
    (hf.trans (D.chartRefinementIso_reconstruction φ ψ α β v p a b w hφ hψ).symm)

end FLT.Mazur.SchemeGeometricDescent.Data
