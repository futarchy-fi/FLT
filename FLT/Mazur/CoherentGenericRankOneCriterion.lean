/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentRankOneDevissage

/-!
# Generic-rank-one criterion for coherent sheaves

Stacks 01YI on a nonempty Noetherian scheme, with the original quantified
witness hypothesis. On an empty scheme the conclusion is instead equivalent
to the zero sheaf having the property.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ZeroObject
open Scheme.Modules FLT.Mazur.CoherentIdealIntersection

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The original witness hypothesis, quantified over every integral closed subscheme. -/
def HasGenericRankOneWitnesses (P : X.Modules → Prop) : Prop :=
  ∀ (J : X.IdealSheafData) (hJ : IsIntegral J.subscheme),
    Nonempty (@GenericRankOneWitness X J hJ P)

/-- Nonemptiness supplies an integral closed subscheme and hence a member of the property class. -/
theorem zero_of_generic_rank_one_witnesses [Nonempty X] {P : X.Modules → Prop}
    (hP : TwoOutOfThree P) (hw : HasGenericRankOneWitnesses P) : P 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let Z : Closeds X := ⟨closure ({x} : Set X), isClosed_closure⟩
  have hZ : IsIrreducible (Z : Set X) := isIrreducible_singleton.closure
  let : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    reducedClosedSubscheme_isIntegral Z hZ
  let w := Classical.choice
    (hw (Scheme.IdealSheafData.vanishingIdeal Z) (reducedClosedSubscheme_isIntegral Z hZ))
  have := w.finite
  exact hP.zero_of_member w.sheaf w.property

/-- Noetherian support induction with the zero base case already established. -/
theorem generic_rank_one_of_zero {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (hw : HasGenericRankOneWitnesses P) (hzero : P 0)
    (M : X.Modules) [M.IsFinitePresentation] : P M := by
  let Q (Z : Closeds X) := ∀ (N : X.Modules), N.IsFinitePresentation → support N ⊆ Z → P N
  suffices h : Q (closedSupport M) from h M inferInstance (Set.Subset.refl _)
  apply closed_induction_on_irreducible Q _ _ _ (closedSupport M)
  · intro N hN hs
    have hz : IsZero N := (support_eq_empty_iff_isZero N).mp (Set.eq_empty_of_subset_empty hs)
    exact hP.iso_of_zero coherent_zero (isZero_zero _) hzero coherent_zero hz.isoZero.symm hzero
  · intro Z W hZ hW N hN hs
    obtain ⟨A, B, f, g, w, h, hA, hB⟩ := exists_supported_decomposition N Z W hs
    exact hP.middle h (hZ A h.finite₁ hA) (hW B h.finite₃ hB)
  · intro Z hZ ih N hN hs
    let w : ClosedRankOneWitness P Z hZ := Classical.choice
      (hw (Scheme.IdealSheafData.vanishingIdeal Z) (reducedClosedSubscheme_isIntegral Z hZ))
    apply rank_one_supported hP Z hZ _ w N hs
    intro W hW _ I
    apply ih W hW ((pushforward (reducedClosedSubschemeι W)).obj (idealModule I))
      (GenericIdealSupport.closedIdeal_coherent
      (Scheme.IdealSheafData.vanishingIdeal W) I)
    simpa using support_closedPushforward_subset_range (reducedClosedSubschemeι W) (idealModule I)

/-- Stacks 01YI for nonempty schemes, with no extra zero or geometric-existence hypothesis. -/
theorem generic_rank_one_devissage [Nonempty X] {P : X.Modules → Prop}
    (hP : TwoOutOfThree P) (hw : HasGenericRankOneWitnesses P)
    (M : X.Modules) [M.IsFinitePresentation] : P M :=
  generic_rank_one_of_zero hP hw (zero_of_generic_rank_one_witnesses hP hw) M

/-- On an empty scheme the conclusion holds exactly when the property contains zero. -/
theorem empty_devissage_iff [IsEmpty X] {P : X.Modules → Prop} (hP : TwoOutOfThree P) :
    (∀ M : X.Modules, M.IsFinitePresentation → P M) ↔ P 0 := by
  refine ⟨fun h ↦ h 0 coherent_zero, fun hzero M _ ↦ ?_⟩
  have hz : IsZero M := (isZero_iff_stalk_isZero M).mpr (fun x ↦ isEmptyElim x)
  exact hP.iso_of_zero coherent_zero (isZero_zero _) hzero coherent_zero hz.isoZero.symm hzero

end FLT.Mazur.FCurve.CoherentDevissage
