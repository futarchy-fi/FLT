/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelSubgroup
public import FLT.Mazur.OddWeierstrassCyclicHomSourceModuli

/-!
# Odd characteristic chart: relabeling descends to the actual cyclic subgroup locus

The multiplication equation is preserved by independent relabeling of the
auxiliary and cyclic labels. Its unique closed-locus lift satisfies the
composition law and retains the actual original modular class.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n)))

/-- The actual relabeling map on the closed subgroup locus. -/
def cyclicHomLocusRelabel :
    cyclicHomUniversalMultiplicationLocus n ⟶ cyclicHomUniversalMultiplicationLocus n :=
  cyclicHomUniversalLocusLift n
    (cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomRelabel n a c).left)
    (cyclicHomRelabel_equation n a c _ (cyclicHomUniversalLocus_equation_zero n))

/-- The closed-locus map retains the exact full relabeled parameter. -/
@[reassoc] theorem cyclicHomLocusRelabel_inclusion :
    cyclicHomLocusRelabel n a c ≫ cyclicHomUniversalMultiplicationLocusInclusion n =
      cyclicHomUniversalMultiplicationLocusInclusion n ≫ (cyclicHomRelabel n a c).left :=
  cyclicHomUniversalLocusLift_inclusion n _ _

/-- Identity relabeling is the identity on the actual subgroup locus. -/
theorem cyclicHomLocusRelabel_one : cyclicHomLocusRelabel n 1 1 = 𝟙 _ := by
  apply (cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)).mp
  rw [cyclicHomLocusRelabel_inclusion, cyclicHomRelabel_one, Over.id_left,
    Category.comp_id, Category.id_comp]

/-- The full locus satisfies the same actual composition law as its two marking factors. -/
theorem cyclicHomLocusRelabel_mul (b : MulAut (Labels 3))
    (d : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusRelabel n (a * b) (c * d) =
      cyclicHomLocusRelabel n b d ≫ cyclicHomLocusRelabel n a c := by
  apply (cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)).mp
  rw [cyclicHomLocusRelabel_inclusion, Category.assoc, cyclicHomLocusRelabel_inclusion,
    cyclicHomLocusRelabel_inclusion_assoc, cyclicHomRelabel_mul, Over.comp_left]

/-- Every relabeled locus test retains its full original ample cyclic modular class. -/
theorem cyclicHomLocusModuliClass_relabel {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    cyclicHomLocusModuliClass n (q ≫ cyclicHomLocusRelabel n a c) =
      cyclicHomLocusModuliClass n q := by
  unfold cyclicHomLocusModuliClass
  have he : (q ≫ cyclicHomLocusRelabel n a c) ≫
      cyclicHomUniversalMultiplicationLocusInclusion n =
        (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n) ≫
          (cyclicHomRelabel n a c).left := by
    rw [Category.assoc, cyclicHomLocusRelabel_inclusion, Category.assoc]
  simp only [he]
  exact cyclicHomSourceModuliClass_relabel n a c _ _

end FLT.Mazur.OddWeierstrassParameter
