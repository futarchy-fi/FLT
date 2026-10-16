/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartFamilyCorrections
public import FLT.Mazur.EquivalenceRelationMixedChartRestriction
public import FLT.Mazur.FiniteGroupOpenCoefficientRefinement
public import FLT.Mazur.InvariantObstructionNaturality

/-!
# Restricting simultaneous chart correction obstructions

Independent smaller stable charts give actual maps on invariant sections,
exact boundary values, and full mixed discrepancies. Their commuting diagram
induces the obstruction map; a solved correction problem stays solved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
open SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary MixedFrames.relation jointBoundaryTarget
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U U' : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ U a = U a)
  (hU' : ∀ a σ, (action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ U' a = U' a)
  (h : ∀ a, U' a ≤ U a)

/-- Restrict each invariant ambient lift to its independently chosen smaller stable chart. -/
def restrictSections : Sections e n o U hU →+ Sections e n o U' hU' where
  toFun v a := FiniteGroupOpenRelation.invariantRestriction
    (action e (Fin (n a)) (o a)) (U a) (hU a) (U' a) (hU' a) (h a) (v a)
  map_zero' := by
    funext a
    exact map_zero _
  map_add' v w := by
    funext a
    exact map_add _ _ _

/-- Restriction on all entire mixed relation coefficient rings. -/
def restrictDifferences :
    (∀ a b, Γ((mixedChartOpen (o a) (o b) (U a) (U b)).toScheme, ⊤)) →+
      ∀ a b, Γ((mixedChartOpen (o a) (o b) (U' a) (U' b)).toScheme, ⊤) where
  toFun v a b :=
    (mixedChartRestriction (o a) (o b) (U a) (U' a) (U b) (U' b) (h a) (h b)).appTop (v a b)
  map_zero' := by
    funext a b
    exact map_zero _
  map_add' v w := by
    funext a b
    exact map_add _ _ _

/-- The same single restricted lift family computes the restricted full discrepancy. -/
theorem difference_restrictSections (v : Sections e n o U hU) :
    difference e n o U' hU' (restrictSections e n o U U' hU hU' h v) =
      restrictDifferences n o U U' h (difference e n o U hU v) := by
  funext a b
  have hf := congrArg (fun f ↦ f.appTop (v a).val)
    (mixedChartRestriction_first (o a) (o b) (U a) (U' a) (U b) (U' b) (h a) (h b))
  have hg := congrArg (fun f ↦ f.appTop (v b).val)
    (mixedChartRestriction_second (o a) (o b) (U a) (U' a) (U b) (U' b) (h a) (h b))
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at hf hg
  change _ - _ =
    (mixedChartRestriction (o a) (o b) (U a) (U' a) (U b) (U' b) (h a) (h b)).appTop (_ - _)
  exact (congrArg₂ (fun x y ↦ x - y) hf.symm hg.symm).trans
    (map_sub (mixedChartRestriction (o a) (o b)
      (U a) (U' a) (U b) (U' b) (h a) (h b)).appTop.hom _ _).symm

variable (i : B ⟶ A)

/-- Restrict exact boundary coefficients along the original closed chart inclusions. -/
def restrictBoundary :
    (∀ a, Γ((InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U a).toScheme, ⊤)) →+
      ∀ a, Γ((InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U' a).toScheme, ⊤) where
  toFun v a := ((InvariantBoundary.boundary (p := p) (q := q) (Fin (n a)) (o a) i).homOfLE
    ((InvariantBoundary.inclusion (Fin (n a)) (o a) i).preimage_mono (h a))).appTop (v a)
  map_zero' := by
    funext a
    exact map_zero _
  map_add' v w := by
    funext a
    exact map_add _ _ _

/-- Restricting invariant lifts commutes with the exact closed boundary map. -/
theorem restriction_restrictSections (v : Sections e n o U hU) :
    restriction e n o U' hU' i (restrictSections e n o U U' hU hU' h v) =
      restrictBoundary n o U U' h i (restriction e n o U hU i v) := by
  funext a
  have hc := congrArg (fun f ↦ f.appTop (v a).val)
    (morphismRestrict_homOfLE (InvariantBoundary.inclusion (Fin (n a)) (o a) i)
      (U' a) (U a) (h a))
  change (InvariantBoundary.inclusion (Fin (n a)) (o a) i ∣_ U' a).appTop
    (FiniteGroupOpenRelation.invariantRestriction (action e (Fin (n a)) (o a))
      (U a) (hU a) (U' a) (hU' a) (h a) (v a)).val = _
  rw [FiniteGroupOpenRelation.invariantRestriction_val]
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
    restrictBoundary, restriction, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hc

/-- The actual induced map of simultaneous obstruction groups under independent refinement. -/
def defectRestriction :=
  InvariantSectionObstruction.map
    (restriction e n o U hU i) (difference e n o U hU)
    (restriction e n o U' hU' i) (difference e n o U' hU')
    (restrictSections e n o U U' hU hU' h) (restrictBoundary n o U U' h i)
    (restrictDifferences n o U U' h)
    (restriction_restrictSections e n o U U' hU hU' h i)
    (difference_restrictSections e n o U U' hU hU' h)

/-- The obstruction of the restricted family is exactly the image of the original obstruction. -/
theorem defectRestriction_defect (v : Sections e n o U hU) :
    defectRestriction e n o U U' hU hU' h i (defect e n o U hU i v) =
      defect e n o U' hU' i (restrictSections e n o U U' hU hU' h v) :=
  InvariantSectionObstruction.map_defect _ _ _ _ _ _ _ _ _ v

/-- Actual simultaneous solvability is preserved under arbitrary independent stable restrictions. -/
theorem defect_zero_restrict (v : Sections e n o U hU) (hv : defect e n o U hU i v = 0) :
    defect e n o U' hU' i (restrictSections e n o U U' hU hU' h v) = 0 := by
  rw [← defectRestriction_defect, hv, map_zero]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
