/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingCoverCoherence

/-!
# Original triple-overlap coherence of the complete marking line

The adjacent and outer pair projections give equal comparisons at each shared
member. Every original pair projection also retains the descended recovery.
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

variable (T : Over (Spec (.of (PowerSeries K))))
  (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)

/-- The original pair routes agree at the middle member, including line compositors. -/
theorem completeMarkingCoverTriple_middle_square (i j k : 𝒰.I₀) :
    LinePullbackSquare (relativeTotalMap f (relativeCoverTriple12 T 𝒰 i j k))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
      (relativeTotalMap f (relativeCoverTriple23 T 𝒰 i j k))
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 j k))
      (by rw [← relativeTotalMap_comp, ← relativeTotalMap_comp]
          exact congrArg (relativeTotalMap f) (relativeCoverTriple23_left T 𝒰 i j k).symm)
      (completeMarkingTestLineIso K n h (relativeCoverPairRight T 𝒰 i j))
      (completeMarkingTestLineIso K n h (relativeCoverTriple12 T 𝒰 i j k))
      (completeMarkingTestLineIso K n h (relativeCoverPairLeft T 𝒰 j k))
      (completeMarkingTestLineIso K n h (relativeCoverTriple23 T 𝒰 i j k)) :=
  completeMarkingTestLineIso_square K n h _ _ _ _ (relativeCoverTriple23_left T 𝒰 i j k).symm

/-- The original pair routes agree at the first member, including line compositors. -/
theorem completeMarkingCoverTriple_first_square (i j k : 𝒰.I₀) :
    LinePullbackSquare (relativeTotalMap f (relativeCoverTriple12 T 𝒰 i j k))
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
      (relativeTotalMap f (relativeCoverTriple13 T 𝒰 i j k))
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i k))
      (by rw [← relativeTotalMap_comp, ← relativeTotalMap_comp]
          exact congrArg (relativeTotalMap f) (relativeCoverTriple13_left T 𝒰 i j k).symm)
      (completeMarkingTestLineIso K n h (relativeCoverPairLeft T 𝒰 i j))
      (completeMarkingTestLineIso K n h (relativeCoverTriple12 T 𝒰 i j k))
      (completeMarkingTestLineIso K n h (relativeCoverPairLeft T 𝒰 i k))
      (completeMarkingTestLineIso K n h (relativeCoverTriple13 T 𝒰 i j k)) :=
  completeMarkingTestLineIso_square K n h _ _ _ _ (relativeCoverTriple13_left T 𝒰 i j k).symm

/-- The original pair routes agree at the last member, including line compositors. -/
theorem completeMarkingCoverTriple_last_square (i j k : 𝒰.I₀) :
    LinePullbackSquare (relativeTotalMap f (relativeCoverTriple23 T 𝒰 i j k))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 j k))
      (relativeTotalMap f (relativeCoverTriple13 T 𝒰 i j k))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 i k))
      (by rw [← relativeTotalMap_comp, ← relativeTotalMap_comp]
          exact congrArg (relativeTotalMap f) (relativeCoverTriple13_right T 𝒰 i j k).symm)
      (completeMarkingTestLineIso K n h (relativeCoverPairRight T 𝒰 j k))
      (completeMarkingTestLineIso K n h (relativeCoverTriple23 T 𝒰 i j k))
      (completeMarkingTestLineIso K n h (relativeCoverPairRight T 𝒰 i k))
      (completeMarkingTestLineIso K n h (relativeCoverTriple13 T 𝒰 i j k)) :=
  completeMarkingTestLineIso_square K n h _ _ _ _ (relativeCoverTriple13_right T 𝒰 i j k).symm

variable {V : Scheme} (s : V ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]

/-- Descended recovery commutes with the original 12 pair projection. -/
theorem completeMarkingCoverTriple12_recovery (i j k : 𝒰.I₀) :
    LinePullbackTriangle (relativeTotalMap f (relativeCoverTriple12 T 𝒰 i j k))
      (pullback.fst f (relativeCoverPair T 𝒰 i j).hom)
      (pullback.fst f (relativeCoverTriple T 𝒰 i j k).hom) (relativeTotalMap_fst _ _)
      (completeMarkingDescendedTestIso K n h s (relativeCoverPair T 𝒰 i j))
      (completeMarkingTestLineIso K n h (relativeCoverTriple12 T 𝒰 i j k))
      (completeMarkingDescendedTestIso K n h s (relativeCoverTriple T 𝒰 i j k)) :=
  completeMarkingDescendedTestIso_triangle K n h s _

/-- Descended recovery commutes with the original 23 pair projection. -/
theorem completeMarkingCoverTriple23_recovery (i j k : 𝒰.I₀) :
    LinePullbackTriangle (relativeTotalMap f (relativeCoverTriple23 T 𝒰 i j k))
      (pullback.fst f (relativeCoverPair T 𝒰 j k).hom)
      (pullback.fst f (relativeCoverTriple T 𝒰 i j k).hom) (relativeTotalMap_fst _ _)
      (completeMarkingDescendedTestIso K n h s (relativeCoverPair T 𝒰 j k))
      (completeMarkingTestLineIso K n h (relativeCoverTriple23 T 𝒰 i j k))
      (completeMarkingDescendedTestIso K n h s (relativeCoverTriple T 𝒰 i j k)) :=
  completeMarkingDescendedTestIso_triangle K n h s _

/-- Descended recovery commutes with the original 13 pair projection. -/
theorem completeMarkingCoverTriple13_recovery (i j k : 𝒰.I₀) :
    LinePullbackTriangle (relativeTotalMap f (relativeCoverTriple13 T 𝒰 i j k))
      (pullback.fst f (relativeCoverPair T 𝒰 i k).hom)
      (pullback.fst f (relativeCoverTriple T 𝒰 i j k).hom) (relativeTotalMap_fst _ _)
      (completeMarkingDescendedTestIso K n h s (relativeCoverPair T 𝒰 i k))
      (completeMarkingTestLineIso K n h (relativeCoverTriple13 T 𝒰 i j k))
      (completeMarkingDescendedTestIso K n h s (relativeCoverTriple T 𝒰 i j k)) :=
  completeMarkingDescendedTestIso_triangle K n h s _

end FLT.Mazur.PolygonInfinitesimalStages
