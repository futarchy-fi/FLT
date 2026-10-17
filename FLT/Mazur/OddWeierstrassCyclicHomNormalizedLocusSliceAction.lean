/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedLocusSlice
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedRelabelAction
public import FLT.Mazur.OddWeierstrassCyclicHomSliceRelabelAction

/-!
# The actual normalized subgroup is invariant inside the full normalized slice

The closed inclusion intertwines both constructed actions. The comparison
retains all original cyclic labels, without a coprimality hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The closed normalized subgroup inclusion commutes with both independent relabelings. -/
@[reassoc] theorem cyclicHomNormalizedLocusToSlice_equivariant
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomNormalizedRelabel n a c ≫ cyclicHomNormalizedLocusToSlice n =
      cyclicHomNormalizedLocusToSlice n ≫ cyclicHomSliceRelabel n a c := by
  simp only [cyclicHomNormalizedRelabel, cyclicHomSliceRelabel, Category.assoc,
    cyclicHomLocusNormalization_toSlice, cyclicHomLocusRelabel_inclusion_assoc,
    cyclicHomNormalizedLocusToSlice_inclusion_assoc]

/-- The full finite group action restricts to the actual closed subgroup locus. -/
theorem cyclicHomNormalizedLocusToSlice_action
    (e : MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) :
    (cyclicHomNormalizedRelabelAction n e).hom ≫ cyclicHomNormalizedLocusToSlice n =
      cyclicHomNormalizedLocusToSlice n ≫ (cyclicHomSliceRelabelAction n e).hom :=
  cyclicHomNormalizedLocusToSlice_equivariant n e.1 e.2

end FLT.Mazur.OddWeierstrassParameter
