/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementMiddle
public import FLT.Mazur.AffineComparisonConjugation
public import FLT.Mazur.SchemeAffineCrossRefinementOuterRestriction

/-!
# Restriction of effective cross-refinement comparisons

Pullback of the effective comparison agrees with comparison on the restricted
cross refinement, through the canonical base pullback composition charts.
-/

open Lean Meta Elab Tactic

-- Keep implicit type arguments separate even when they are definitionally equal.
-- Fixing them during congruence makes the kernel unfold large pullback constructions.
private meta partial def structuralCongr (g : MVarId) (fuel : Nat) : MetaM (List MVarId) :=
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let sides : Option (Expr × Expr) := match t.eq? with
      | some (_, a, b) => some (a, b)
      | none => t.heq?.map fun (_, a, _, b) => (a, b)
    let some (a, b) := sides | return [g]
    if a == b then
      try g.refl; return [] catch _ =>
        try g.hrefl; return [] catch _ => return [g]
    if fuel == 0 then return [g]
    if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.isApp then
      if let some gs ← g.hcongr? then
        return (← gs.mapM fun h => structuralCongr h (fuel - 1)).flatten
    return [g]
local elab "structural_hcongr" : tactic => liftMetaTactic fun g => structuralCongr g 12

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
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent]

attribute [local irreducible] Chart.comparison middleComparison

/-- The effective cross comparison commutes with restriction of both base and cover rings. -/
theorem effectiveComparison_restrict :
    (pullback (Spec.map α)).map (ρ.effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom =
      (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom ≫
        ((ρ.restrict ψ α β v hψ).effectiveComparison D).hom := by
  have h := AffineComparisonConjugation.restriction (pullback (Spec.map α))
    (C.comparison ρ.leftChart D ρ.leftRefinement) (ρ.middleComparison D)
    (C'.comparison ρ.rightChart D ρ.rightRefinement)
    (C.comparison (ρ.restrict ψ α β v hψ).leftChart D
      (ρ.restrict ψ α β v hψ).leftRefinement)
    ((ρ.restrict ψ α β v hψ).middleComparison D)
    (C'.comparison (ρ.restrict ψ α β v hψ).rightChart D
      (ρ.restrict ψ α β v hψ).rightRefinement)
    (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D))
    (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D))
    (ρ.leftChart.comparison _ D (ρ.restrictLeft ψ α β v hψ))
    (ρ.rightChart.comparison _ D (ρ.restrictRight ψ α β v hψ))
    (by
      have hs := ρ.leftComparison_restrict ψ α β v hψ D
      refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq hs) ?_))
      all_goals structural_hcongr <;> rfl)
    (by
      have hs := ρ.middleComparison_restrict ψ α β v hψ D
      refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq hs) ?_))
      all_goals structural_hcongr <;> rfl)
    (by
      have hs := ρ.rightComparison_restrict ψ α β v hψ D
      refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq hs) ?_))
      all_goals structural_hcongr <;> rfl)
  have hl : HEq
      ((pullback (Spec.map α)).map (ρ.effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom)
      ((pullback (Spec.map α)).map
          (C.comparison ρ.leftChart D ρ.leftRefinement ≪≫ ρ.middleComparison D ≪≫
            (C'.comparison ρ.rightChart D ρ.rightRefinement).symm).hom ≫
        (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom) := by
    structural_hcongr
    all_goals rfl
  have hr : HEq
      ((AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom ≫
        ((ρ.restrict ψ α β v hψ).effectiveComparison D).hom)
      ((AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom ≫
        (C.comparison (ρ.restrict ψ α β v hψ).leftChart D
            (ρ.restrict ψ α β v hψ).leftRefinement ≪≫
          (ρ.restrict ψ α β v hψ).middleComparison D ≪≫
          (C'.comparison (ρ.restrict ψ α β v hψ).rightChart D
            (ρ.restrict ψ α β v hψ).rightRefinement).symm).hom) := by
    structural_hcongr
    all_goals rfl
  exact eq_of_heq (hl.trans ((heq_of_eq h).trans hr.symm))

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
