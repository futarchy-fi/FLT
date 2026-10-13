/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomLocusRelabel
public import FLT.Mazur.CyclicHomNormalizedModuli

/-!
# The two marking groups act on the actual subgroup locus

Inverse relabeling gives the inverse actual scheme map. The resulting action
preserves original modular classes, also after full normalization to the
closed normalized subgroup chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Independent auxiliary and cyclic relabelings give actual automorphisms of the closed locus. -/
def cyclicHomLocusRelabelAut
    (e : MulAut (Labels 4) × MulAut (Multiplicative (ZMod n))) :
    Aut (cyclicHomUniversalMultiplicationLocus n) where
  hom := cyclicHomLocusRelabel n e.1 e.2
  inv := cyclicHomLocusRelabel n e.1⁻¹ e.2⁻¹
  hom_inv_id := by
    rw [← cyclicHomLocusRelabel_mul, inv_mul_cancel, inv_mul_cancel,
      cyclicHomLocusRelabel_one]
  inv_hom_id := by
    rw [← cyclicHomLocusRelabel_mul, mul_inv_cancel, mul_inv_cancel,
      cyclicHomLocusRelabel_one]

/-- The product marking group acts on the scheme-theoretic cyclic subgroup locus. -/
def cyclicHomLocusRelabelAction :
    (MulAut (Labels 4) × MulAut (Multiplicative (ZMod n))) →*
      Aut (cyclicHomUniversalMultiplicationLocus n) where
  toFun := cyclicHomLocusRelabelAut n
  map_one' := by
    apply Aut.ext
    exact cyclicHomLocusRelabel_one n
  map_mul' e d := by
    apply Aut.ext
    exact cyclicHomLocusRelabel_mul n e.1 e.2 d.1 d.2

/-- Relabeling and then normalizing retains the exact original non-etale modular class. -/
theorem cyclicHomNormalizedModuliMap_relabel
    (a : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n)))
    {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomMultiplicationEquation n f = 0) :
    (cyclicHomNormalizedModuliMap n).app (Opposite.op T)
      (ULift.up (cyclicHomNormalizedLocusPoint n (f ≫ (cyclicHomRelabel n a c).left)
        (cyclicHomRelabel_equation n a c f h))) = cyclicHomSourceModuliClass n f h := by
  rw [cyclicHomNormalizedModuliMap_normalization, cyclicHomSourceModuliClass_relabel]

end FLT.Mazur.UniversalWeierstrass
