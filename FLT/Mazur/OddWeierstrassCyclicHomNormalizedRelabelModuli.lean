/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedRelabelAction
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedModuli
public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabelAction

/-!
# The normalized product action retains original ample cyclic modular classes

Equivariance describes every relabeled normalization on the actual closed
subgroup locus. Its modular map is invariant under the entire product action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Relabeling a locus test and then normalizing is the normalized action on its image. -/
theorem cyclicHomNormalizedRelabel_test {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    (q ≫ cyclicHomLocusRelabel n a c) ≫ cyclicHomLocusNormalization n =
      (q ≫ cyclicHomLocusNormalization n) ≫ cyclicHomNormalizedRelabel n a c := by
  simp only [Category.assoc, cyclicHomLocusNormalization_equivariant]

/-- The natural normalization map preserves the actual original modular class on every test. -/
theorem cyclicHomNormalizedModuliMap_locusNormalization {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    (cyclicHomNormalizedModuliMap n).app (Opposite.op T)
      (ULift.up (q ≫ cyclicHomLocusNormalization n)) = cyclicHomLocusModuliClass n q := by
  rw [cyclicHomLocusNormalization_comp, cyclicHomNormalizedModuliMap_normalization]
  rfl

/-- Both independent relabelings preserve the full original modular class on the closed slice. -/
theorem cyclicHomNormalizedModuliMap_action {T : Scheme}
    (q : T ⟶ cyclicHomNormalizedLocus n)
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    (cyclicHomNormalizedModuliMap n).app (Opposite.op T)
        (ULift.up (q ≫ cyclicHomNormalizedRelabel n a c)) =
      (cyclicHomNormalizedModuliMap n).app (Opposite.op T) (ULift.up q) := by
  change (cyclicHomNormalizedModuliMap n).app (Opposite.op T)
    (ULift.up (q ≫ cyclicHomNormalizedLocusInclusion n ≫ cyclicHomLocusRelabel n a c ≫
      cyclicHomLocusNormalization n)) = _
  rw [← Category.assoc q, ← Category.assoc
    (q ≫ cyclicHomNormalizedLocusInclusion n), cyclicHomNormalizedModuliMap_locusNormalization,
    cyclicHomLocusModuliClass_relabel]
  rfl

end FLT.Mazur.OddWeierstrassParameter
