/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteOpenCoefficients
public import FLT.Mazur.EquivalenceRelationMixedChartTests

/-!
# Complete chart coefficients on the actual full mixed relation

An invariant function on a complete stable chart agrees along every original
arrow between arbitrary tests of that chart. In particular its two pullbacks
to the full mixed chart scheme agree, including the original scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U)
  (hc : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)
  (t : invariantCoordinates (restrictedAction (action e I o) U hU))

include e hc in
/-- Every original-arrow test preserves coefficients on a complete stable chart. -/
theorem completeOpen_invariant_test {T : Scheme.{0}} (u v : T ⟶ U.toScheme) (a : T ⟶ D)
    (ha : a ≫ p = u ≫ U.ι ≫ first p q I o)
    (hb : a ≫ q = v ≫ U.ι ≫ first p q I o) : u.appTop t.val = v.appTop t.val := by
  have h := congrArg (fun b ↦ (SourceRestriction.lift U.ι U.ι u v a ha hb).appTop b)
    (completeOpen_invariant_equalizes e I o U hU hc t)
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    SourceRestriction.lift_fst, SourceRestriction.lift_snd] using h

include e hc in
/-- The full self-mixed relation equation is constructed from moving invariance and completeness. -/
theorem completeOpen_invariant_mixed :
    (MixedFrames.mixedChartFirst o o U U).appTop t.val =
      (MixedFrames.mixedChartSecond o o U U).appTop t.val := by
  apply completeOpen_invariant_test e I o U hU hc t
    (MixedFrames.mixedChartFirst o o U U) (MixedFrames.mixedChartSecond o o U U)
    ((MixedFrames.mixedChartOpen o o U U).ι ≫ MixedFrames.arrow p q I I o o)
  · rw [Category.assoc, MixedFrames.arrow_first]
    simp only [MixedFrames.mixedChartFirst, Scheme.Hom.resLE_comp_ι_assoc]
  · rw [Category.assoc, MixedFrames.arrow_second]
    simp only [MixedFrames.mixedChartSecond, Scheme.Hom.resLE_comp_ι_assoc]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
