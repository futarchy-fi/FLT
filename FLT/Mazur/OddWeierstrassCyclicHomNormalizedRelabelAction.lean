/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomLocusRelabelNormalization

/-!
# Both marking groups act on the actual normalized closed subgroup locus

Relabeling followed by normalization defines actual scheme automorphisms.
Absorption supplies the composition laws and normalization equivariance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Relabel both markings and normalize the actual retained subgroup parameter. -/
def cyclicHomNormalizedRelabel
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomNormalizedLocus n ⟶ cyclicHomNormalizedLocus n :=
  cyclicHomNormalizedLocusInclusion n ≫ cyclicHomLocusRelabel n a c ≫
    cyclicHomLocusNormalization n

/-- Normalization intertwines both actual relabeling actions. -/
@[reassoc] theorem cyclicHomLocusNormalization_equivariant
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomLocusNormalization n ≫ cyclicHomNormalizedRelabel n a c =
      cyclicHomLocusRelabel n a c ≫ cyclicHomLocusNormalization n :=
  cyclicHomLocusNormalization_relabel n a c

/-- Identity relabeling fixes the original normalized closed subgroup locus. -/
theorem cyclicHomNormalizedRelabel_one : cyclicHomNormalizedRelabel n 1 1 = 𝟙 _ := by
  rw [cyclicHomNormalizedRelabel, cyclicHomLocusRelabel_one, Category.id_comp,
    cyclicHomNormalizedLocusInclusion_normalization]

/-- The normalized scheme maps obey the full product action composition law. -/
theorem cyclicHomNormalizedRelabel_mul
    (a b : MulAut (Labels 3)) (c d : MulAut (Multiplicative (ZMod n))) :
    cyclicHomNormalizedRelabel n (a * b) (c * d) =
      cyclicHomNormalizedRelabel n b d ≫ cyclicHomNormalizedRelabel n a c := by
  unfold cyclicHomNormalizedRelabel
  rw [Category.assoc, Category.assoc, cyclicHomLocusNormalization_relabel,
    cyclicHomLocusRelabel_mul, Category.assoc]

/-- Inverse labels give an actual inverse on the normalized non-etale subgroup locus. -/
def cyclicHomNormalizedRelabelAut
    (e : MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) :
    Aut (cyclicHomNormalizedLocus n) where
  hom := cyclicHomNormalizedRelabel n e.1 e.2
  inv := cyclicHomNormalizedRelabel n e.1⁻¹ e.2⁻¹
  hom_inv_id := by
    rw [← cyclicHomNormalizedRelabel_mul, inv_mul_cancel, inv_mul_cancel,
      cyclicHomNormalizedRelabel_one]
  inv_hom_id := by
    rw [← cyclicHomNormalizedRelabel_mul, mul_inv_cancel, mul_inv_cancel,
      cyclicHomNormalizedRelabel_one]

/-- The two independent marking groups act on the original normalized closed subgroup locus. -/
def cyclicHomNormalizedRelabelAction :
    (MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) →*
      Aut (cyclicHomNormalizedLocus n) where
  toFun := cyclicHomNormalizedRelabelAut n
  map_one' := by
    apply Aut.ext
    exact cyclicHomNormalizedRelabel_one n
  map_mul' e d := by
    apply Aut.ext
    exact cyclicHomNormalizedRelabel_mul n e.1 d.1 e.2 d.2

end FLT.Mazur.OddWeierstrassParameter
