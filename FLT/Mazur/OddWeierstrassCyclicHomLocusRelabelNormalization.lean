/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelNormalization
public import FLT.Mazur.OddWeierstrassCyclicHomLocusNormalizationRetraction
public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabel

/-!
# Absorption on the actual closed subgroup locus

Full parameter absorption and uniqueness of closed-locus factorizations give
the actual normalization/relabeling equality of scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The global normalization map retains the normalized full parameter at every locus test. -/
@[reassoc] theorem cyclicHomLocusNormalization_parameter {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    q ≫ cyclicHomLocusNormalization n ≫ cyclicHomNormalizedLocusInclusion n ≫
        cyclicHomUniversalMultiplicationLocusInclusion n =
      cyclicHomNormalizedPoint n (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n) := by
  rw [← Category.assoc q, cyclicHomLocusNormalization_comp,
    cyclicHomNormalizedLocusPoint_parameter]

/-- Normalization absorbs intermediate normalization before both independent relabelings. -/
theorem cyclicHomLocusNormalization_relabel
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusNormalization n ≫ cyclicHomNormalizedLocusInclusion n ≫
        cyclicHomLocusRelabel n a c ≫ cyclicHomLocusNormalization n =
      cyclicHomLocusRelabel n a c ≫ cyclicHomLocusNormalization n := by
  apply (cancel_mono (cyclicHomNormalizedLocusInclusion n)).mp
  apply (cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)).mp
  simp only [Category.assoc]
  rw [← Category.assoc (cyclicHomLocusNormalization n),
    ← Category.assoc (cyclicHomLocusNormalization n ≫ cyclicHomNormalizedLocusInclusion n),
    cyclicHomLocusNormalization_parameter, cyclicHomLocusNormalization_parameter]
  simp only [Category.assoc, cyclicHomLocusRelabel_inclusion]
  rw [← Category.assoc _ _ (cyclicHomRelabel n a c).left]
  have hp := cyclicHomLocusNormalization_parameter n
    (𝟙 (cyclicHomUniversalMultiplicationLocus n))
  simp only [Category.id_comp] at hp
  rw [← Category.assoc (cyclicHomLocusNormalization n), hp]
  exact cyclicHomNormalizedPoint_relabel_normalize n a c _

end FLT.Mazur.OddWeierstrassParameter
