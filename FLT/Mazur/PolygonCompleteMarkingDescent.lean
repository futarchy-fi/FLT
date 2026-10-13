/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingTestLine
public import FLT.Mazur.SchemeDescentSheafIso
public import FLT.Mazur.SchemeLineCanonicalFunctor

/-!
# Actual positive marking-line descent for the complete smoothing family

The geometric marking line on a parameter test carries its actual double
and triple overlap datum. Its comparison with the original complete-family
line is an isomorphism of descent data, not only of Picard classes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard SchemeGeometricDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking completeMarkingLineBaseChangeIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))

/-- The original complete positive marking line as an actual line bundle. -/
def completeMarkingLineObject : LineBundleCat (exactVeroneseProj K n h) :=
  ⟨completeMarkingLine K n h, completeMarkingLine_rankOne K n h⟩

/-- Full geometric descent on the actual positive line of the pulled-back marking. -/
def completeMarkingDescentData :
    Data (pullback.fst (exactVeroneseProjToBase K n h) s)
      (completeFiberMarkingLine K n h s) :=
  (canonical _ (completeMarkingLine K n h)).ofIso _ (completeMarkingLineBaseChangeIso K n h s)

/-- The original pulled-back marked line and its proved geometric descent laws. -/
def completeMarkingLineDatum :
    LineData (pullback.fst (exactVeroneseProjToBase K n h) s) where
  obj := completeFiberMarkingLine K n h s
  rankOne := EffectiveCartier.divisorLineBundle_locallyFreeRankOne
    (completeFiberMarkingDivisor_relativeCartier K n h s).1
  datum := completeMarkingDescentData K n h s

/-- The actual comparison identifies canonical descent with the full marking-line datum. -/
def completeMarkingCanonicalIso :
    (lineCanonical (pullback.fst (exactVeroneseProjToBase K n h) s)).obj
      (completeMarkingLineObject K n h) ≅ completeMarkingLineDatum K n h s :=
  LineData.isoMk _ (completeMarkingLineBaseChangeIso K n h s)
    ((canonical _ (completeMarkingLine K n h)).ofIso_compatible _ _)

/-- The descent comparison retains the specified section-preserving sheaf isomorphism. -/
theorem completeMarkingCanonicalIso_hom :
    (completeMarkingCanonicalIso K n h s).hom.val =
      (completeMarkingLineBaseChangeIso K n h s).hom := rfl

/-- The full-family marking overlap has the actual diagonal identity. -/
theorem completeMarkingDescent_diagonal :
    Diagonal (pullback.fst (exactVeroneseProjToBase K n h) s)
      (completeFiberMarkingLine K n h s) (completeMarkingDescentData K n h s).overlap :=
  (completeMarkingDescentData K n h s).diagonal

/-- The full-family marking overlap satisfies the actual triple-overlap cocycle. -/
theorem completeMarkingDescent_cocycle :
    Cocycle (pullback.fst (exactVeroneseProjToBase K n h) s)
      (completeFiberMarkingLine K n h s) (completeMarkingDescentData K n h s).overlap :=
  (completeMarkingDescentData K n h s).cocycle

end FLT.Mazur.PolygonInfinitesimalStages
