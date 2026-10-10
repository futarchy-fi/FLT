/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementEffectiveRestriction

/-!
# Independence of further covering maps

Two restrictions through the same new affine base may choose different
covering rings and different maps of the old covering ring. Their effective
comparisons agree: the restriction square determines both through the same
base composition chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {A B T : CommRingCat.{u}} (ψ : A ⟶ B) (χ : A ⟶ T)
variable (α : ρ.baseRing ⟶ A) (β : ρ.coverRing ⟶ B) (γ : ρ.coverRing ⟶ T)
variable (v : ρ.ringMap ≫ β = α ≫ ψ) (w : ρ.ringMap ≫ γ = α ≫ χ)
variable (hψ : ψ.hom.FaithfullyFlat) (hχ : χ.hom.FaithfullyFlat)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict χ α γ w hχ).leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict χ α γ w hχ).rightChart.cover).obj M).IsQuasicoherent]
attribute [local irreducible] effectiveComparison AffineRefinementPullback.compositionChart

/-- Covering maps may differ while their effective comparison stays the same. -/
theorem effectiveComparison_restrict_cover_independent :
    ((ρ.restrict ψ α β v hψ).effectiveComparison D).hom =
      ((ρ.restrict χ α γ w hχ).effectiveComparison D).hom := by
  apply (cancel_epi
    (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom).mp
  exact (ρ.effectiveComparison_restrict ψ α β v hψ D).symm.trans
    (ρ.effectiveComparison_restrict χ α γ w hχ D)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
