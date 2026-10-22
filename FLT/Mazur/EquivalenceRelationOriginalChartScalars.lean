/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationOrbitSchemeArrows
public import FLT.Mazur.RingPairInvariantFlatScalars

/-!
# The prescribed original scalar map on normalized affine charts

The original full relation equalizer maps to the normalized chart invariants
by the literal endpoint pullback. This supplies the original scalar map for
the orbit construction; it does not assert that its image is the full fixed ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarOrbitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "R₀" => RingPairInvariantFlatScalars.invariants p.appTop.hom q.appTop.hom

/-- Every original equalized coefficient is fixed by the actual restricted moving action. -/
theorem originalChartScalar_fixed (a : R₀) (g : Equiv.Perm I) :
    (ρ g).hom.appTop ((U.ι ≫ first p q I o).appTop a.val) =
      (U.ι ≫ first p q I o).appTop a.val := by
  change (((U.ι ≫ first p q I o).appTop ≫ (ρ g).hom.appTop) a.val) = _
  rw [← Scheme.Hom.comp_appTop, ← Category.assoc, restrictedAction_hom_ι,
    Category.assoc, ← actionArrow_second e]
  have ha := congrArg (fun v ↦ (U.ι ≫ actionArrow I o g).appTop v) a.property.symm
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    Category.assoc, actionArrow_first] using ha

/-- The chart scalar homomorphism is constructed from the full original relation equalizer. -/
def originalChartScalars : R₀ →+* invariantCoordinates ρ := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  refine ((U.ι ≫ first p q I o).appTop.hom.comp (Subring.subtype R₀)).codRestrict _ ?_
  intro a g
  exact originalChartScalar_fixed e I o U hU a g⁻¹

/-- This is the exact original endpoint pullback, with no replacement of the scalar ring. -/
@[simp] theorem originalChartScalars_val (a : R₀) :
    (originalChartScalars e I o U hU a).val = (U.ι ≫ first p q I o).appTop a.val := rfl

/-- Every original arrow between chart tests equalizes the constructed original scalars. -/
theorem originalChartScalars_test {T : Scheme.{0}} (u v : T ⟶ U.toScheme)
    (d : T ⟶ D) (hp : d ≫ p = u ≫ U.ι ≫ first p q I o)
    (hq : d ≫ q = v ≫ U.ι ≫ first p q I o) (a : R₀) :
    u.appTop (originalChartScalars e I o U hU a).val =
      v.appTop (originalChartScalars e I o U hU a).val := by
  have h := congrArg (fun b ↦ d.appTop b) a.property
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hp, hq,
    originalChartScalars_val] using h

end FLT.Mazur.EquivalenceRelationNormalizedFrames
