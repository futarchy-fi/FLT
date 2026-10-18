/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSheaf
public import FLT.Mazur.CyclicCharacteristicDisjointAction

/-!
# The parameter presheaf and the actual disjoint source scheme

A parameter with a fixed characteristic choice gives a map into the actual
scheme coproduct. This map of presheaves is locally bijective: an arbitrary
test splits over the two open components, and different component choices
can agree only on an empty test. Thus disconnected tests are handled locally.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- A fixed-chart parameter gives a test of the actual disjoint source scheme. -/
def parameterToDisjointSource :
    normalizedParameterPresheaf n ⟶ uliftYoneda.{1}.obj (normalizedDisjointSource n) where
  app _ := ↾(fun q ↦ ULift.up (q.2.down ≫ normalizedDisjointInclusion n q.1))
  naturality _ _ _ := by
    ext q
    exact congrArg ULift.up (Category.assoc _ _ _)

/-- Every actual test of the disjoint scheme locally selects a characteristic chart. -/
instance parameterToDisjointSource_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (parameterToDisjointSource n) where
  imageSieve_mem {T} f := by
    let C := (sigmaOpenCover (normalizedLocus n)).pullback₁ f.down
    apply Scheme.fppfTopology.superset_covering _
      (Precoverage.generate_mem_toGrothendieck
        (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ C.mem₀))
    apply (Sieve.generate_le_iff _ _).mpr
    rintro U g ⟨i⟩
    refine ⟨⟨i, ULift.up (pullback.snd f.down (normalizedDisjointInclusion n i))⟩, ?_⟩
    exact congrArg ULift.up pullback.condition.symm

/-- Equality of actual source tests identifies fixed-chart parameters fppf locally. -/
instance parameterToDisjointSource_isLocallyInjective :
    Presheaf.IsLocallyInjective Scheme.fppfTopology (parameterToDisjointSource n) where
  equalizerSieve_mem {T} q r h := by
    obtain ⟨b, q⟩ := q
    obtain ⟨c, r⟩ := r
    have he : q.down ≫ normalizedDisjointInclusion n b =
        r.down ≫ normalizedDisjointInclusion n c := congrArg ULift.down h
    by_cases hbc : b = c
    · subst c
      have hqr : q = r := ULift.ext ((cancel_mono _).mp he)
      subst r
      simpa only [Presheaf.equalizerSieve_self_eq_top] using Scheme.fppfTopology.top_mem T.unop
    · let _ : IsEmpty T.unop := isEmpty_of_commSq_sigmaι_of_ne ⟨he⟩ hbc
      exact Scheme.fppfTopology.superset_covering bot_le
        (Scheme.bot_mem_grothendieckTopology T.unop)

/-- The parameter-to-source comparison becomes invertible after fppf sheafification. -/
theorem parameterToDisjointSource_sheafification_isIso :
    IsIso ((presheafToSheaf Scheme.fppfTopology (Type 1)).map
      (parameterToDisjointSource n)) :=
  (Scheme.fppfTopology.W_iff _).mp
    (Scheme.fppfTopology.W_of_isLocallyBijective (parameterToDisjointSource n))

end FLT.Mazur.CyclicCharacteristicAtlas
