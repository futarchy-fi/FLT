/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedClosingUnit
public import FLT.Mazur.LaurentScaledNilpotentReparametrization

/-!
# The full retained closing parameter is an automorphism

The exact tangent power supplies the scaled reciprocal reduction. This
constructs the inverse of the original parameter, including its full roots.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (a : Fin k)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "J" => ideal Q (parameter R π m)
local notation "K" => Ideal.map (algebraMap Q L) J
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "v" => arithmeticRetainedClosingUnit data H m k hk a

/-- The full reciprocal parameter differs from its tangent power only in the coefficient ideal. -/
theorem arithmeticRetainedClosingUnit_sub_tangent_mem :
    (v : L) - algebraMap Q L (↑(A ^ (2 * (a.val + 1))) : Q) *
      LaurentPolynomial.T (-1) ∈ K := by
  apply Ideal.Quotient.eq.mp
  have h := congrArg Units.val (arithmeticRetainedClosingUnit_reduction data H m k hk a
    (S := L ⧸ K) (Ideal.Quotient.mk K) (by rw [Ideal.mk_ker]))
  change Ideal.Quotient.mk K (v : L) =
    Ideal.Quotient.mk K (algebraMap Q L (↑(A ^ (2 * (a.val + 1))) : Q)) *
      Ideal.Quotient.mk K (LaurentPolynomial.T (-1)) at h
  exact h.trans (map_mul _ _ _).symm

/-- The inverse of the actual full retained closing substitution is constructed. -/
def arithmeticRetainedClosingEquiv : L ≃ₐ[Q] L :=
  LaurentScaledNilpotentReparametrization.equiv J (arithmeticParameterIdeal_nilpotent π m)
    (A ^ (2 * (a.val + 1))) v
    (arithmeticRetainedClosingUnit_sub_tangent_mem data H m k hk a)

/-- The constructed equivalence evaluates at the exact full closing unit. -/
theorem arithmeticRetainedClosingEquiv_toAlgHom :
    (arithmeticRetainedClosingEquiv data H m k hk a).toAlgHom =
      LaurentUnitPoints.evalUnit v := rfl

/-- The entire retained parameter map is an isomorphism of the original branch torus. -/
instance arithmeticRetainedClosingParameter_isIso :
    IsIso (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q) v).toRingHom)) := by
  let e := arithmeticRetainedClosingEquiv data H m k hk a
  change IsIso (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
