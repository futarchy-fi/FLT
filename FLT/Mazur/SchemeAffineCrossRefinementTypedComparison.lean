/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementComparison
public import FLT.Mazur.SchemeAffineCrossRefinementRestriction

/-!
# Typed comparisons for geometric restrictions

Fix the ambient module categories before forming comparison composites. Each
isomorphism is the existing geometric comparison with an explicit base ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {A B : CommRingCat.{u}} (ψ : A ⟶ B)
variable (α : ρ.baseRing ⟶ A) (β : ρ.coverRing ⟶ B)
variable (v : ρ.ringMap ≫ β = α ≫ ψ) (hψ : ψ.hom.FaithfullyFlat)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [hL : ((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [hR : ((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [hL' : ((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent]
variable [hR' : ((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent]

attribute [local irreducible] middleComparison Chart.comparison
attribute [local irreducible] SchemeGeometricDescent.Data.chartSheaf
attribute [local irreducible] SchemeGeometricDescent.Data.chartCrossCoverIso
attribute [local irreducible] SchemeGeometricDescent.Data.chartRefinementIsoTo

/-- The middle comparison with the ambient module category fixed explicitly. -/
def sourceMiddleIso : @Iso (Spec ρ.baseRing).Modules _
    (ρ.leftChart.sheaf D) (ρ.rightChart.sheaf D) := ρ.middleComparison D

omit hL hR in
/-- The restricted middle comparison in the module category of the new base. -/
def targetMiddleIso : @Iso (Spec A).Modules _
    ((ρ.restrict ψ α β v hψ).leftChart.sheaf D)
    ((ρ.restrict ψ α β v hψ).rightChart.sheaf D) :=
  (ρ.restrict ψ α β v hψ).middleComparison D

omit hR hR' in
/-- The left branch comparison with its base pullback expressed by the ring map. -/
def restrictionLeftIso : @Iso (Spec A).Modules _
    ((pullback (Spec.map α)).obj (ρ.leftChart.sheaf D))
    ((ρ.restrict ψ α β v hψ).leftChart.sheaf D) :=
  ρ.leftChart.comparison _ D (ρ.restrictLeft ψ α β v hψ)

omit hL hL' in
/-- The right branch comparison retains the independent covering map. -/
def restrictionRightIso : @Iso (Spec A).Modules _
    ((pullback (Spec.map α)).obj (ρ.rightChart.sheaf D))
    ((ρ.restrict ψ α β v hψ).rightChart.sheaf D) :=
  ρ.rightChart.comparison _ D (ρ.restrictRight ψ α β v hψ)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
