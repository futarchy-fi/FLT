/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementCanonical
public import FLT.Mazur.SchemeAffineCrossRefinementCoverIndependence

/-!
# Comparison is independent of the chosen common affine cover

Equal base rings and equal maps from the two original base charts suffice.
The common covering rings and both maps from the original covering charts
may be chosen independently. Equality is heterogeneous only to allow the
base rings and their sheaf categories to be presented independently.
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
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback σ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback σ.rightChart.cover).obj M).IsQuasicoherent]

/-- Equality of geometric cross refinements transports the effective comparison. -/
theorem effectiveComparison_heq_of_eq (h : ρ = σ) :
    HEq (ρ.effectiveComparison D).hom (σ.effectiveComparison D).hom := by
  subst σ
  rfl

variable [((pullback ρ.canonical.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.canonical.rightChart.cover).obj M).IsQuasicoherent]

/-- The independently chosen covering rings do not affect the effective comparison. -/
theorem effectiveComparison_cover_choice_independent
    (hbase : ρ.baseRing = σ.baseRing)
    (hl : HEq ρ.leftBase σ.leftBase) (hr : HEq ρ.rightBase σ.rightBase) :
    HEq (ρ.effectiveComparison D).hom (σ.effectiveComparison D).hom := by
  let _ : ((pullback (ρ.canonical.restrict ρ.ringMap (𝟙 ρ.baseRing) ρ.fromCanonical
      ρ.fromCanonical_square ρ.faithfullyFlat).leftChart.cover).obj M).IsQuasicoherent := by
    rw [ρ.canonical_restrict]
    infer_instance
  let _ : ((pullback (ρ.canonical.restrict ρ.ringMap (𝟙 ρ.baseRing) ρ.fromCanonical
      ρ.fromCanonical_square ρ.faithfullyFlat).rightChart.cover).obj M).IsQuasicoherent := by
    rw [ρ.canonical_restrict]
    infer_instance
  let _ : ((pullback (σ.canonical.restrict σ.ringMap (𝟙 σ.baseRing) σ.fromCanonical
      σ.fromCanonical_square σ.faithfullyFlat).leftChart.cover).obj M).IsQuasicoherent := by
    rw [σ.canonical_restrict]
    infer_instance
  let _ : ((pullback (σ.canonical.restrict σ.ringMap (𝟙 σ.baseRing) σ.fromCanonical
      σ.fromCanonical_square σ.faithfullyFlat).rightChart.cover).obj M).IsQuasicoherent := by
    rw [σ.canonical_restrict]
    infer_instance
  have hρ := effectiveComparison_heq_of_eq _ ρ D ρ.canonical_restrict
  have hσ := effectiveComparison_heq_of_eq _ σ D σ.canonical_restrict
  cases ρ with
  | mk R S φ hφ l r u v hu hv w =>
    cases σ with
    | mk R' T ψ hψ l' r' u' v' hu' hv' w' =>
      dsimp only at hbase hl hr
      cases hbase
      cases eq_of_heq hl
      cases eq_of_heq hr
      let _ : ((pullback ((canonical (mk R S φ hφ l r u v hu hv w)).restrict
          ψ (𝟙 R) (fromCanonical (mk R T ψ hψ l r u' v' hu' hv' w'))
          (fromCanonical_square
            (mk R T ψ hψ l r u' v' hu' hv' w')) hψ).leftChart.cover).obj M).IsQuasicoherent := by
        change ((pullback ((canonical (mk R T ψ hψ l r u' v' hu' hv' w')).restrict
          ψ (𝟙 R) (fromCanonical (mk R T ψ hψ l r u' v' hu' hv' w'))
          (fromCanonical_square
            (mk R T ψ hψ l r u' v' hu' hv' w')) hψ).leftChart.cover).obj M).IsQuasicoherent
        infer_instance
      let _ : ((pullback ((canonical (mk R S φ hφ l r u v hu hv w)).restrict
          ψ (𝟙 R) (fromCanonical (mk R T ψ hψ l r u' v' hu' hv' w'))
          (fromCanonical_square
            (mk R T ψ hψ l r u' v' hu' hv' w')) hψ).rightChart.cover).obj M).IsQuasicoherent := by
        change ((pullback ((canonical (mk R T ψ hψ l r u' v' hu' hv' w')).restrict
          ψ (𝟙 R) (fromCanonical (mk R T ψ hψ l r u' v' hu' hv' w'))
          (fromCanonical_square
            (mk R T ψ hψ l r u' v' hu' hv' w')) hψ).rightChart.cover).obj M).IsQuasicoherent
        infer_instance
      have h := effectiveComparison_restrict_cover_independent
        (canonical (mk R S φ hφ l r u v hu hv w)) φ ψ (𝟙 R)
          (fromCanonical (mk R S φ hφ l r u v hu hv w))
          (fromCanonical (mk R T ψ hψ l r u' v' hu' hv' w'))
          (fromCanonical_square (mk R S φ hφ l r u v hu hv w))
          (fromCanonical_square (mk R T ψ hψ l r u' v' hu' hv' w')) hφ hψ D
      exact hρ.symm.trans ((heq_of_eq h).trans hσ)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
