/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationSubgroup
public import FLT.Mazur.OddWeierstrassCyclicHomLocusEquationUniversal
public import FLT.Mazur.OddWeierstrassCyclicHomSliceFunctor

/-!
# The normalized closed locus of actual cyclic subgroups

Intersect the actual multiplication locus with the inverse image of the
closed auxiliary normalized slice. The full normalization of every subgroup
parameter factors through this intersection on its unchanged test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The closed normalized locus retains the actual multiplication equation. -/
def cyclicHomNormalizedLocus : Scheme :=
  pullback (cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomAuxiliary n).left)
    normalizedSliceInclusion

/-- Forget normalization while retaining the actual subgroup parameter. -/
def cyclicHomNormalizedLocusInclusion :
    cyclicHomNormalizedLocus n ⟶ cyclicHomUniversalMultiplicationLocus n :=
  pullback.fst _ _

/-- The normalized subgroup locus is closed inside the actual subgroup locus. -/
instance cyclicHomNormalizedLocusInclusion_isClosedImmersion :
    IsClosedImmersion (cyclicHomNormalizedLocusInclusion n) := by
  dsimp [cyclicHomNormalizedLocusInclusion]
  infer_instance

variable {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)

/-- The full normalized parameter factors through the actual subgroup locus. -/
def cyclicHomNormalizedLocusParameter : T ⟶ cyclicHomUniversalMultiplicationLocus n :=
  cyclicHomUniversalLocusLift n (cyclicHomNormalizedPoint n f)
    (cyclicHomNormalization_equation n f h)

/-- The subgroup factorization keeps the entire normalized marking. -/
@[reassoc] theorem cyclicHomNormalizedLocusParameter_inclusion :
    cyclicHomNormalizedLocusParameter n f h ≫ cyclicHomUniversalMultiplicationLocusInclusion n =
      cyclicHomNormalizedPoint n f :=
  cyclicHomUniversalLocusLift_inclusion n _ _

/-- The actual normalized subgroup gives a point of the intersection of the two closed loci. -/
def cyclicHomNormalizedLocusPoint : T ⟶ cyclicHomNormalizedLocus n :=
  pullback.lift (cyclicHomNormalizedLocusParameter n f h)
    (auxiliarySchemeNormalizedSlicePoint (cyclicHomAuxiliaryPoint n f)) (by
      rw [← Category.assoc, cyclicHomNormalizedLocusParameter_inclusion,
        cyclicHomNormalizedPoint_auxiliary, auxiliarySchemeNormalizedSlicePoint_inclusion])

/-- The intersection point retains the actual normalized subgroup parameter. -/
@[reassoc] theorem cyclicHomNormalizedLocusPoint_inclusion :
    cyclicHomNormalizedLocusPoint n f h ≫ cyclicHomNormalizedLocusInclusion n =
      cyclicHomNormalizedLocusParameter n f h :=
  pullback.lift_fst _ _ _

/-- The intersection point retains every auxiliary and cyclic label after normalization. -/
@[reassoc] theorem cyclicHomNormalizedLocusPoint_parameter :
    cyclicHomNormalizedLocusPoint n f h ≫ cyclicHomNormalizedLocusInclusion n ≫
      cyclicHomUniversalMultiplicationLocusInclusion n = cyclicHomNormalizedPoint n f := by
  rw [← Category.assoc, cyclicHomNormalizedLocusPoint_inclusion,
    cyclicHomNormalizedLocusParameter_inclusion]

end FLT.Mazur.OddWeierstrassParameter
