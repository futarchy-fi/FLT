/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverRefinement

/-!
# Recognition of refined cross-cover comparison squares

Named isomorphisms can be recognized separately before applying the refinement theorem.
This keeps geometric chart projections out of the reconstruction argument.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
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

variable [((pullback b').obj M).IsQuasicoherent]
variable [((pullback c').obj M).IsQuasicoherent]

/-- Recognized effective isomorphisms inherit the cross-cover refinement square. -/
theorem chartCrossCoverIso_refinement_of_eq
    (e : D.chartSheaf φ p a b wb hφ ≅ D.chartSheaf φ p a c wc hφ)
    (e' : D.chartSheaf ψ p a' b' wb' hψ ≅ D.chartSheaf ψ p a' c' wc' hψ)
    (l : (pullback (Spec.map α)).obj (D.chartSheaf φ p a b wb hφ) ≅
      D.chartSheaf ψ p a' b' wb' hψ)
    (r : (pullback (Spec.map α)).obj (D.chartSheaf φ p a c wc hφ) ≅
      D.chartSheaf ψ p a' c' wc' hψ)
    (he : e = D.chartCrossCoverIso φ p a b c wb wc hφ)
    (he' : e' = D.chartCrossCoverIso ψ p a' b' c' wb' wc' hψ)
    (hl : l = D.chartRefinementIsoTo φ ψ α β v p a b wb hφ hψ a' b' ha hb wb')
    (hr : r = D.chartRefinementIsoTo φ ψ α β v p a c wc hφ hψ a' c' ha hc wc') :
    (pullback (Spec.map α)).map e.hom ≫ r.hom = l.hom ≫ e'.hom := by
  subst e e' l r
  exact D.chartCrossCoverIso_refinement φ ψ α β v p a b c wb wc hφ hψ
    a' b' c' ha hb hc wb' wc'

end FLT.Mazur.SchemeGeometricDescent.Data
