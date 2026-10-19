/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalMap

/-!
# Original evaluations of the rational source-kernel map

Every nonidentity evaluation factors through the actual affine summand. The
identity factors through the complementary quotient and maps to the zero section.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- Nonzero original labels define evaluations on the rational affine quotient. -/
def primeKernelAffineEvaluation (i : ZMod p) (hi : i ≠ 0) :
    PrimeKernelAffineAlgebra E p q hq hfixed →ₐ[ℚ] AlgebraicClosure ℚ :=
  Ideal.Quotient.liftₐ _ (primeKernelDescentEvaluation E p q hq hfixed i) (by
    change _ ≤ RingHom.ker (primeKernelDescentEvaluation E p q hq hfixed i).toRingHom
    rw [Ideal.span_le]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    change primeKernelDescentEvaluation E p q hq hfixed i
      (primeKernelIdentity E p q hq hfixed) = 0
    rw [primeKernelIdentity_evaluation, ite_eq_right hi])

/-- The affine evaluation restricts to the unchanged original rational evaluation. -/
theorem primeKernelAffineEvaluation_comp (i : ZMod p) (hi : i ≠ 0) :
    (primeKernelAffineEvaluation E p q hq hfixed i hi).comp
      (primeKernelAffineQuotient E p q hq hfixed) =
        primeKernelDescentEvaluation E p q hq hfixed i := by
  ext a
  rfl

/-- The resulting affine point has the original abscissa. -/
@[simp] theorem primeKernelAffineEvaluation_x (i : ZMod p) (hi : i ≠ 0) :
    primeKernelAffineEvaluation E p q hq hfixed i hi
      (primeKernelAffineQuotient E p q hq hfixed (primeKernelX E p q hq hfixed)) =
        xCoord (primeKernelParam E p q hq i) :=
  primeKernelX_evaluation E p q hq hfixed i

/-- The resulting affine point has the original ordinate. -/
@[simp] theorem primeKernelAffineEvaluation_y (i : ZMod p) (hi : i ≠ 0) :
    primeKernelAffineEvaluation E p q hq hfixed i hi
      (primeKernelAffineQuotient E p q hq hfixed (primeKernelY E p q hq hfixed)) =
        yCoord (primeKernelParam E p q hq i) :=
  primeKernelY_evaluation E p q hq hfixed i

/-- The actual rational scheme map takes nonzero evaluations through their original affine chart. -/
@[reassoc] theorem primeKernelRationalMap_evaluation_ne_zero (i : ZMod p) (hi : i ≠ 0) :
    Spec.map (CommRingCat.ofHom
      (primeKernelDescentEvaluation E p q hq hfixed i).toRingHom) ≫
        primeKernelRationalMap E p q hq hfixed =
      Spec.map (CommRingCat.ofHom
        ((primeKernelAffineEvaluation E p q hq hfixed i hi).comp
          (primeKernelAffineChart E p q hq hfixed)).toRingHom) ≫ integralCurveChart E 2 := by
  rw [← primeKernelAffineEvaluation_comp E p q hq hfixed i hi]
  change Spec.map (CommRingCat.ofHom
    ((primeKernelAffineEvaluation E p q hq hfixed i hi).toRingHom.comp
      (primeKernelAffineQuotient E p q hq hfixed).toRingHom)) ≫ _ =
    Spec.map (CommRingCat.ofHom
      ((primeKernelAffineEvaluation E p q hq hfixed i hi).toRingHom.comp
        (primeKernelAffineChart E p q hq hfixed).toRingHom)) ≫ _
  simp only [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [Category.assoc, primeKernelRationalMap_affine, Category.assoc]

/-- The identity evaluation factors through the complementary infinity quotient. -/
def primeKernelInfinityEvaluation :
    PrimeKernelInfinityAlgebra E p q hq hfixed →ₐ[ℚ] AlgebraicClosure ℚ :=
  Ideal.Quotient.liftₐ _ (primeKernelDescentEvaluation E p q hq hfixed 0) (by
    change _ ≤ RingHom.ker (primeKernelDescentEvaluation E p q hq hfixed 0).toRingHom
    rw [Ideal.span_le]
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    change primeKernelDescentEvaluation E p q hq hfixed 0
      (1 - primeKernelIdentity E p q hq hfixed) = 0
    simp only [map_sub, map_one, primeKernelIdentity_evaluation, ite_true, sub_self])

/-- The identity is taken to the actual zero section of the original rational cubic. -/
@[reassoc] theorem primeKernelRationalMap_evaluation_zero :
    Spec.map (CommRingCat.ofHom
      (primeKernelDescentEvaluation E p q hq hfixed 0).toRingHom) ≫
        primeKernelRationalMap E p q hq hfixed =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ integralCurveZero E := by
  have he : (primeKernelInfinityEvaluation E p q hq hfixed).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {1 - primeKernelIdentity E p q hq hfixed})) =
      (primeKernelDescentEvaluation E p q hq hfixed 0).toRingHom := by
    ext a
    rfl
  rw [← he]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    primeKernelRationalMap_infinity, ← Category.assoc]
  congr 1
  exact specAlgHom_structure (primeKernelInfinityEvaluation E p q hq hfixed)

end WeierstrassCurve.Velu
