/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDescentTransportRefinement
public import FLT.Mazur.SchemeAffineCrossCoverDescent
public import FLT.Mazur.SchemeAffineChartNamedRefinement

/-!
# Effective cross-cover comparison under affine refinement

The comparison descended from the original transport commutes with simultaneous
base and cover refinement. The two covering maps remain independent. Equality
is detected by reconstruction on the faithfully flat refined cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentTransportRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem reconstruction_transport_of_eq
    {R S R' S' : CommRingCat.{u}}
    (φ : R ⟶ S) (ψ : R' ⟶ S') (α : R ⟶ R') (β : S ⟶ S')
    (v : φ ≫ β = α ≫ ψ) {X Y : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules}
    (D : SchemeGeometricDescent.Data p M)
    (b c : Spec S ⟶ Y) (w : b ≫ p = c ≫ p)
    (b' c' : Spec S' ⟶ Y) (hb : Spec.map β ≫ b = b') (hc : Spec.map β ≫ c = c')
    (w' : b' ≫ p = c' ≫ p) {A B : (Spec R).Modules}
    (e₀ : (pullback (Spec.map φ)).obj A ≅ (pullback b).obj M)
    (e₁ : (pullback (Spec.map φ)).obj B ≅ (pullback c).obj M)
    (E₀ : (pullback (Spec.map ψ)).obj ((pullback (Spec.map α)).obj A) ≅
      (pullback b').obj M)
    (E₁ : (pullback (Spec.map ψ)).obj ((pullback (Spec.map α)).obj B) ≅
      (pullback c').obj M)
    (h₀ : E₀ = AffineNamedRefinementReconstruction.chart φ ψ α β v b b' hb e₀)
    (h₁ : E₁ = AffineNamedRefinementReconstruction.chart φ ψ α β v c c' hc e₁)
    (f : A ⟶ B) (hf : (pullback (Spec.map φ)).map f ≫ e₁.hom =
      e₀.hom ≫ (D.transport b c w).hom) :
    (pullback (Spec.map ψ)).map ((pullback (Spec.map α)).map f) ≫ E₁.hom =
      E₀.hom ≫ (D.transport b' c' w').hom := by
  rw [h₀, h₁]
  exact reconstruction_transport φ ψ α β v D b c w b' c' hb hc w' e₀ e₁ f hf
end FLT.Mazur.AffineDescentTransportRefinement

namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (α : R ⟶ R') (β : S ⟶ S')
variable (v : φ ≫ β = α ≫ ψ)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b c : Spec S ⟶ Y)
variable (wb : Spec.map φ ≫ a = b ≫ p) (wc : Spec.map φ ≫ a = c ≫ p)
variable (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)
variable (a' : Spec R' ⟶ X) (b' c' : Spec S' ⟶ Y)
variable (ha : Spec.map α ≫ a = a')
variable (hb : Spec.map β ≫ b = b') (hc : Spec.map β ≫ c = c')
variable (wb' : Spec.map ψ ≫ a' = b' ≫ p) (wc' : Spec.map ψ ≫ a' = c' ≫ p)
variable [((pullback b).obj M).IsQuasicoherent] [((pullback c).obj M).IsQuasicoherent]

attribute [local irreducible] chartCrossCoverIso chartRefinementIsoTo chartReconstruction

/-- Reconstructing the restricted comparison gives transport on the refined covering maps. -/
@[reassoc]
theorem chartCrossCoverIso_refined_reconstruction :
    (pullback (Spec.map ψ)).map
        ((pullback (Spec.map α)).map (D.chartCrossCoverIso φ p a b c wb wc hφ).hom) ≫
        (D.chartRefinementReconstructionTo φ ψ α β v p a c wc hφ c' hc).hom =
      (D.chartRefinementReconstructionTo φ ψ α β v p a b wb hφ b' hb).hom ≫
        (D.transport b' c' (wb'.symm.trans wc')).hom :=
  AffineDescentTransportRefinement.reconstruction_transport_of_eq φ ψ α β v D
    b c (wb.symm.trans wc) b' c' hb hc (wb'.symm.trans wc')
    (D.chartReconstruction φ p a b wb hφ) (D.chartReconstruction φ p a c wc hφ)
    (D.chartRefinementReconstructionTo φ ψ α β v p a b wb hφ b' hb)
    (D.chartRefinementReconstructionTo φ ψ α β v p a c wc hφ c' hc)
    (by unfold chartReconstruction; rfl) (by unfold chartReconstruction; rfl)
    (D.chartCrossCoverIso φ p a b c wb wc hφ).hom
    (D.chartCrossCoverIso_reconstruction φ p a b c wb wc hφ)

variable [((pullback b').obj M).IsQuasicoherent] [((pullback c').obj M).IsQuasicoherent]
attribute [local irreducible] chartRefinementReconstructionTo

/-- Effective cross-cover comparison is compatible with further base and cover refinement. -/
@[reassoc]
theorem chartCrossCoverIso_refinement :
    (pullback (Spec.map α)).map (D.chartCrossCoverIso φ p a b c wb wc hφ).hom ≫
        (D.chartRefinementIsoTo φ ψ α β v p a c wc hφ hψ a' c' ha hc wc').hom =
      (D.chartRefinementIsoTo φ ψ α β v p a b wb hφ hψ a' b' ha hb wb').hom ≫
        (D.chartCrossCoverIso ψ p a' b' c' wb' wc' hψ).hom := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback α
    (D.chartSheaf φ p a b wb hφ)
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique ψ hψ
    (D.chartReconstruction ψ p a' c' wc' hψ)
  rw [Functor.map_comp, Category.assoc, D.chartRefinementIsoTo_reconstruction,
    Functor.map_comp, Category.assoc, D.chartCrossCoverIso_reconstruction,
    D.chartRefinementIsoTo_reconstruction_assoc]
  exact D.chartCrossCoverIso_refined_reconstruction φ ψ α β v p a b c wb wc hφ
    a' b' c' hb hc wb' wc'

end FLT.Mazur.SchemeGeometricDescent.Data
