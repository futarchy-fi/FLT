/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedChartTests
public import FLT.Mazur.FiniteGroupOpenRelationCoefficients

/-!
# Compatible normalized chart scalars from original invariant functions

Pullback of an original invariant function constructs invariant coefficients on
every stable chart. Full mixed compatibility follows from the original arrow,
without restrictions on frame sizes or distinguished labels.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source MixedFrames.relation
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : A.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)
  (s : Γ(W.toScheme, ⊤)) (hs : (p ∣_ W).appTop s = (q.resLE W _ hW.le).appTop s)

include hs in
omit [IsSeparated p] in
/-- Original invariance holds on every arrow test over the actual open domain. -/
theorem open_scalar_test {T : Scheme.{0}} (u v : T ⟶ W.toScheme) (a : T ⟶ D)
    (ha : a ≫ p = u ≫ W.ι) (hb : a ≫ q = v ≫ W.ι) : u.appTop s = v.appTop s := by
  let l := (isPullback_morphismRestrict p W).flip.lift a u ha
  have hl : l ≫ (p ⁻¹ᵁ W).ι = a := (isPullback_morphismRestrict p W).flip.lift_fst _ _ _
  have hu : l ≫ (p ∣_ W) = u := (isPullback_morphismRestrict p W).flip.lift_snd _ _ _
  have hv : l ≫ q.resLE W _ hW.le = v := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hl, hb]
  have hh := congrArg (fun coeff ↦ l.appTop coeff) hs
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hu, hv] using hh

variable {I : Type} [Fintype I] (o : I) (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U) (hUW : U ≤ first p q I o ⁻¹ᵁ W)

/-- The chart scalar is constructed from the original function and actual moving action. -/
def openChartScalar : invariantCoordinates (restrictedAction (action e I o) U hU) :=
  FiniteGroupOpenRelation.invariantCoefficient (action e I o) (first p q I o) p q
    (actionArrow I o) (actionArrow_first I o) (actionArrow_second e I o)
    W hW U hU hUW s hs

/-- The constructed invariant scalar is the unchanged original coefficient pullback. -/
theorem openChartScalar_val :
    (openChartScalar e W hW s hs o U hU hUW).val = (first p q I o |>.resLE W U hUW).appTop s :=
  rfl

variable {J : Type} [Fintype J] (o' : J) (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V) (hVW : V ≤ first p q J o' ⁻¹ᵁ W)

/-- Independently indexed scalar coefficients agree on the entire mixed relation. -/
theorem openChartScalar_compatible :
    (MixedFrames.mixedChartFirst o o' U V).appTop
        (openChartScalar e W hW s hs o U hU hUW).val =
      (MixedFrames.mixedChartSecond o o' U V).appTop
        (openChartScalar e W hW s hs o' V hV hVW).val := by
  apply open_scalar_test W hW s hs
    (MixedFrames.mixedChartFirst o o' U V ≫ (first p q I o).resLE W U hUW)
    (MixedFrames.mixedChartSecond o o' U V ≫ (first p q J o').resLE W V hVW)
    ((MixedFrames.mixedChartOpen o o' U V).ι ≫ MixedFrames.arrow p q I J o o')
  · simp only [Category.assoc, MixedFrames.arrow_first, Scheme.Hom.resLE_comp_ι,
      MixedFrames.mixedChartFirst, Scheme.Hom.resLE_comp_ι_assoc]
  · simp only [Category.assoc, MixedFrames.arrow_second, Scheme.Hom.resLE_comp_ι,
      MixedFrames.mixedChartSecond, Scheme.Hom.resLE_comp_ι_assoc]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
