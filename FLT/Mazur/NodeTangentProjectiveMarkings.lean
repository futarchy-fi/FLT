/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentProjectiveLineDescent

/-!
# Original ordered normalization markings under actual root exchange

The complete semilinear operation exchanges the two original slope sections
0 and -a. These are equalities of scheme sections with coefficient conjugation,
not only a permutation of their geometric points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur
open ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [Fact (Irreducible (nodeTangentPolynomial W))]
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "σ" => RingEquiv.toRingHom (AlgEquiv.toRingEquiv (nodeTangentConjugation W))
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)

/-- Every original affine slope section has the actual semilinear translated image. -/
@[reassoc] theorem nodeTangentLineConjugation_slope (c : S) :
    infinitySlopeMark c ≫ nodeTangentLineConjugation W =
      Spec.map (CommRingCat.ofHom σ) ≫ infinitySlopeMark (σ c - a) := by
  simp only [infinitySlopeMark, Category.assoc, nodeTangentLineConjugation_left]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change aeval c (nodeTangentNormalizationConjugation W (C r)) =
      σ (aeval (σ c - a) (C r))
    rw [nodeTangentNormalizationConjugation_C, aeval_C, aeval_C]
    rfl
  · change aeval c (nodeTangentNormalizationConjugation W X) =
      σ (aeval (σ c - a) X)
    rw [nodeTangentNormalizationConjugation_X, map_add, aeval_X, aeval_C,
      aeval_X, map_sub]
    have hi : σ (σ c) = c := nodeTangentConjugationHom_involutive W c
    rw [hi, show σ a = -a from nodeTangentShear_a₁_conjugate W, sub_neg_eq_add]
    rfl

/-- The first original node marking goes to the second over the actual coefficient exchange. -/
@[reassoc] theorem nodeTangentLineConjugation_first :
    infinitySlopeMark (0 : S) ≫ nodeTangentLineConjugation W =
      Spec.map (CommRingCat.ofHom σ) ≫ infinitySlopeMark (-a) := by
  simpa only [map_zero, zero_sub] using nodeTangentLineConjugation_slope W 0

/-- The companion original marking returns to the first over the same coefficient exchange. -/
@[reassoc] theorem nodeTangentLineConjugation_second :
    infinitySlopeMark (-a) ≫ nodeTangentLineConjugation W =
      Spec.map (CommRingCat.ofHom σ) ≫ infinitySlopeMark (0 : S) := by
  have h : σ (-a) - a = 0 := by
    rw [map_neg, show σ a = -a from nodeTangentShear_a₁_conjugate W, neg_neg, sub_self]
  simpa only [h] using nodeTangentLineConjugation_slope W (-a)

end FLT.Mazur
