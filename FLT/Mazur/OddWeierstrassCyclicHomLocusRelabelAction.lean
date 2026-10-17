/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabel

/-!
# Odd characteristic chart: the two marking groups act on the actual subgroup locus

Inverse relabeling gives the inverse actual scheme map. The resulting action
preserves original modular classes, including non-etale subgroups
in characteristic two.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Independent auxiliary and cyclic relabelings give actual automorphisms of the closed locus. -/
def cyclicHomLocusRelabelAut
    (e : MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) :
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
    (MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) →*
      Aut (cyclicHomUniversalMultiplicationLocus n) where
  toFun := cyclicHomLocusRelabelAut n
  map_one' := by
    apply Aut.ext
    exact cyclicHomLocusRelabel_one n
  map_mul' e d := by
    apply Aut.ext
    exact cyclicHomLocusRelabel_mul n e.1 e.2 d.1 d.2

/-- The actual odd-chart action preserves the original modular class on every test. -/
theorem cyclicHomLocusModuliClass_action {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (e : MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusModuliClass n (q ≫ (cyclicHomLocusRelabelAction n e).hom) =
      cyclicHomLocusModuliClass n q :=
  cyclicHomLocusModuliClass_relabel n e.1 e.2 q

end FLT.Mazur.OddWeierstrassParameter
