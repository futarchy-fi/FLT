/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSliceRelabelNormalization

/-!
# Both marking groups act on the actual normalized full closed slice

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

/-- Relabel both markings and normalize the actual full cyclic parameter. -/
def cyclicHomSliceRelabel
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomNormalizedSlice n ⟶ cyclicHomNormalizedSlice n :=
  cyclicHomNormalizedSliceInclusion n ≫ (cyclicHomRelabel n a c).left ≫
    cyclicHomNormalizationMorphism n

/-- Normalization intertwines both actual relabeling actions. -/
@[reassoc] theorem cyclicHomNormalizationMorphism_equivariant
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomNormalizationMorphism n ≫ cyclicHomSliceRelabel n a c =
      (cyclicHomRelabel n a c).left ≫ cyclicHomNormalizationMorphism n :=
  cyclicHomNormalizationMorphism_relabel n a c

/-- Identity relabeling fixes the original normalized full closed slice. -/
theorem cyclicHomSliceRelabel_one : cyclicHomSliceRelabel n 1 1 = 𝟙 _ := by
  rw [cyclicHomSliceRelabel, cyclicHomRelabel_one, Over.id_left, Category.id_comp,
    cyclicHomNormalizedSliceInclusion_normalization]

/-- The normalized scheme maps obey the full product action composition law. -/
theorem cyclicHomSliceRelabel_mul
    (a b : MulAut (Labels 3)) (c d : MulAut (Multiplicative (ZMod n))) :
    cyclicHomSliceRelabel n (a * b) (c * d) =
      cyclicHomSliceRelabel n b d ≫ cyclicHomSliceRelabel n a c := by
  unfold cyclicHomSliceRelabel
  rw [Category.assoc, Category.assoc, cyclicHomNormalizationMorphism_relabel,
    cyclicHomRelabel_mul, Over.comp_left, Category.assoc]

/-- Inverse labels give an actual inverse on the normalized unrestricted parameter. -/
def cyclicHomSliceRelabelAut
    (e : MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) :
    Aut (cyclicHomNormalizedSlice n) where
  hom := cyclicHomSliceRelabel n e.1 e.2
  inv := cyclicHomSliceRelabel n e.1⁻¹ e.2⁻¹
  hom_inv_id := by
    rw [← cyclicHomSliceRelabel_mul, inv_mul_cancel, inv_mul_cancel,
      cyclicHomSliceRelabel_one]
  inv_hom_id := by
    rw [← cyclicHomSliceRelabel_mul, mul_inv_cancel, mul_inv_cancel,
      cyclicHomSliceRelabel_one]

/-- The two independent marking groups act on the original normalized full closed slice. -/
def cyclicHomSliceRelabelAction :
    (MulAut (Labels 3) × MulAut (Multiplicative (ZMod n))) →*
      Aut (cyclicHomNormalizedSlice n) where
  toFun := cyclicHomSliceRelabelAut n
  map_one' := by
    apply Aut.ext
    exact cyclicHomSliceRelabel_one n
  map_mul' e d := by
    apply Aut.ext
    exact cyclicHomSliceRelabel_mul n e.1 d.1 e.2 d.2

end FLT.Mazur.OddWeierstrassParameter
