/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementChoiceIndependence
public import FLT.Mazur.SchemeAffineCrossRefinementQuasicoherent

/-!
# Independent cross refinements after affine base restriction

A comparison restricted to a new affine base agrees with a comparison chosen
independently there. The new covering ring and its two covering maps need not
factor through the old common cover. Heterogeneous equality allows independent
presentations of the two base maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p}
variable (ρ σ : C.CrossRefinement C')
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] effectiveComparison AffineRefinementPullback.compositionChart

/-- Transport a restricted comparison into the composite base coordinates. -/
theorem effectiveComparison_restrict_conjugate
    {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    (α : ρ.baseRing ⟶ A) (β : ρ.coverRing ⟶ B)
    (v : ρ.ringMap ≫ β = α ≫ ψ) (hψ : ψ.hom.FaithfullyFlat) :
    (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).inv ≫
        (pullback (Spec.map α)).map (ρ.effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom =
      ((ρ.restrict ψ α β v hψ).effectiveComparison D).hom := by
  rw [ρ.effectiveComparison_restrict ψ α β v hψ D, Iso.inv_hom_id_assoc]

/-- Arbitrary new common covers give the base restriction of the old comparison. -/
theorem effectiveComparison_base_choice_independent (α : ρ.baseRing ⟶ σ.baseRing)
    (hl : ρ.leftBase ≫ α = σ.leftBase) (hr : ρ.rightBase ≫ α = σ.rightBase) :
    HEq
      ((AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).inv ≫
        (pullback (Spec.map α)).map (ρ.effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom)
      (σ.effectiveComparison D).hom := by
  have h := ρ.effectiveComparison_restrict_conjugate D (Limits.pushout.inl α ρ.ringMap)
    α (Limits.pushout.inr α ρ.ringMap) Limits.pushout.condition.symm
    (ρ.leftChart.baseChange_faithfullyFlat α)
  exact (heq_of_eq h).trans
    ((ρ.baseChange α).effectiveComparison_cover_choice_independent σ D rfl
      (heq_of_eq hl) (heq_of_eq hr))

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
