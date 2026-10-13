/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingDescendedTest
public import FLT.Mazur.RelativePicardCoverTriples

/-!
# Marking recovery on the original cover and its pair overlaps

Covering maps and both original pair projections retain the descended recovery
triangle. The two routes from a pair to its covered test give the same actual
positive-line comparison, with the original total-space equality retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking completeMarkingGluedLine relativeTotalMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "f" => exactVeroneseProjToBase K n h

/-- A commuting square of actual tests gives the exact marked-line square. -/
theorem completeMarkingTestLineIso_square
    {A B C D : Over (Spec (.of (PowerSeries K)))}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D) (w : a ≫ b = c ≫ d) :
    LinePullbackSquare (relativeTotalMap f a) (relativeTotalMap f b)
      (relativeTotalMap f c) (relativeTotalMap f d)
      (by rw [← relativeTotalMap_comp, w, relativeTotalMap_comp])
      (completeMarkingTestLineIso K n h b) (completeMarkingTestLineIso K n h a)
      (completeMarkingTestLineIso K n h d) (completeMarkingTestLineIso K n h c) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeMarkingTestLineIso_section K n h b) (completeMarkingTestLineIso_section K n h a)
    (completeMarkingTestLineIso_section K n h d) (completeMarkingTestLineIso_section K n h c)

variable (T : Over (Spec (.of (PowerSeries K))))
  (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)

/-- The original pair projections commute on the actual complete-family marked lines. -/
theorem completeMarkingCoverPair_square (i j : 𝒰.I₀) :
    LinePullbackSquare (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
      (relativeTotalMap f (relativeCoverArrow T 𝒰 i))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
      (relativeTotalMap f (relativeCoverArrow T 𝒰 j))
      (by rw [← relativeTotalMap_comp, relativeCoverPair_condition, relativeTotalMap_comp])
      (completeMarkingTestLineIso K n h (relativeCoverArrow T 𝒰 i))
      (completeMarkingTestLineIso K n h (relativeCoverPairLeft T 𝒰 i j))
      (completeMarkingTestLineIso K n h (relativeCoverArrow T 𝒰 j))
      (completeMarkingTestLineIso K n h (relativeCoverPairRight T 𝒰 i j)) :=
  completeMarkingTestLineIso_square K n h _ _ _ _ (relativeCoverPair_condition T 𝒰 i j)

variable {V : Scheme} (s : V ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]

/-- Recovery commutes with each original total-space covering map. -/
theorem completeMarkingCover_recovery (i : 𝒰.I₀) :
    LinePullbackTriangle (relativeTotalMap f (relativeCoverArrow T 𝒰 i))
      (pullback.fst f T.hom) (pullback.fst f (relativeCoverMember T 𝒰 i).hom)
      (relativeTotalMap_fst _ _) (completeMarkingDescendedTestIso K n h s T)
      (completeMarkingTestLineIso K n h (relativeCoverArrow T 𝒰 i))
      (completeMarkingDescendedTestIso K n h s (relativeCoverMember T 𝒰 i)) :=
  completeMarkingDescendedTestIso_triangle K n h s _

/-- The first original pair projection retains the same descended recovery. -/
theorem completeMarkingCoverPair_left_recovery (i j : 𝒰.I₀) :
    LinePullbackTriangle (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
      (pullback.fst f (relativeCoverMember T 𝒰 i).hom)
      (pullback.fst f (relativeCoverPair T 𝒰 i j).hom) (relativeTotalMap_fst _ _)
      (completeMarkingDescendedTestIso K n h s (relativeCoverMember T 𝒰 i))
      (completeMarkingTestLineIso K n h (relativeCoverPairLeft T 𝒰 i j))
      (completeMarkingDescendedTestIso K n h s (relativeCoverPair T 𝒰 i j)) :=
  completeMarkingDescendedTestIso_triangle K n h s _

/-- The second original pair projection retains the same descended recovery. -/
theorem completeMarkingCoverPair_right_recovery (i j : 𝒰.I₀) :
    LinePullbackTriangle (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
      (pullback.fst f (relativeCoverMember T 𝒰 j).hom)
      (pullback.fst f (relativeCoverPair T 𝒰 i j).hom) (relativeTotalMap_fst _ _)
      (completeMarkingDescendedTestIso K n h s (relativeCoverMember T 𝒰 j))
      (completeMarkingTestLineIso K n h (relativeCoverPairRight T 𝒰 i j))
      (completeMarkingDescendedTestIso K n h s (relativeCoverPair T 𝒰 i j)) :=
  completeMarkingDescendedTestIso_triangle K n h s _

end FLT.Mazur.PolygonInfinitesimalStages
