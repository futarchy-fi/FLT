/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianMarkings
public import FLT.Mazur.PolygonCompleteMarkingDivisor
public import FLT.Mazur.RelativeCartierOriginalSquare
public import FLT.Mazur.SectionCartesianKernel

/-!
# Single marked divisors on the original Cartesian polygon family

Each original label supplies its own relative Cartier ideal on every specified
base-change square. The ideal comparison is the canonical pullback map, including
on singular fibers; no smooth presentation or replacement marking is chosen.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The specified marking has exactly the pulled-back original section ideal. -/
theorem completeCartesianMarking_ker (i : Fin n) :
    (completeBaseMarking K n h i).ker.comap p =
      (completeCartesianMarking K n h s p q hs i).ker := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact section_ker_comap_of_cartesian hs _ _
    (completeCartesianMarking_snd K n h s p q hs i)
    (completeBaseMarking_toBase K n h i)
    (completeCartesianMarking_fst K n h s p q hs i)

/-- Every single original label remains a relative Cartier divisor on the chosen square. -/
theorem completeCartesianMarking_relativeCartier (i : Fin n) :
    RelativeEffectiveCartier q (completeCartesianMarking K n h s p q hs i).ker := by
  rw [← completeCartesianMarking_ker]
  exact relativeCartier_originalSquare hs _ (completeBaseMarking_relativeCartier K n h i)

include hs in
/-- The actual ideal comparison, rather than just its support, is invertible. -/
theorem completeCartesianPointIdeal_isIso (i : Fin n) :
    IsIso (idealModulePullbackHom (completeBaseMarking K n h i).ker p) :=
  relativeCartierIdealPullback_originalSquare hs _
    (completeBaseMarking_relativeCartier K n h i)

/-- The support is precisely the retained labeled section. -/
theorem completeCartesianMarking_support (i : Fin n) :
    ((completeCartesianMarking K n h s p q hs i).ker.support : Set Y) =
      Set.range (completeCartesianMarking K n h s p q hs i) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  exact support_section_ker q _ (completeCartesianMarking_snd K n h s p q hs i)

end FLT.Mazur.PolygonInfinitesimalStages
