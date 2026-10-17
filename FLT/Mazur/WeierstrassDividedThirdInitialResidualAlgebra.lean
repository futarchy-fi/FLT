/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialBaseParameter
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasEdge
public import FLT.Mazur.WeierstrassDividedThirdIncomingCancellation
public import FLT.Mazur.LaurentReciprocalErrorConjugation

/-!
# The full depth-one initial residual as an algebra equivalence

The original Mobius/right parameter remains between the initial positive
factor and both predecessor factors. At layer three only the extra factors
cancel; the entire original parameter remains.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "V" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu
local notation "P" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu
local notation "A" => fun b ↦ correctionPunctureFactor R π m τ (V b) true
local notation "O" => arithmeticSecondPrecedingOpposite hπ data H m j hj u hu
local notation "N" => fun b ↦ twoBranchCorrectionPunctureFactor R π m (s b) (P b) false
local notation "B" => arithmeticInitialBaseEquiv data H m j hj

/-- The complete depth-one residual, with every factor in contravariant algebra order. -/
def arithmeticThirdInitialEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (((N b).trans (O b)).trans B).trans (A b).symm

/-- The algebra residual is precisely the complete original global edge residual. -/
theorem arithmeticThirdInitialEquiv_spec (b : Bool) :
    (punctureSpecIso (arithmeticThirdInitialEquiv hπ data H j hj u hu m b)).hom =
      arithmeticThirdInitialResidual hπ data H m j hj u hu b := by
  simp only [arithmeticThirdInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, arithmeticInitialBaseEquiv_spec,
    arithmeticThirdInitialResidual, Category.assoc]

omit m in
/-- The third layer cancels all added factors and retains the full original base parameter. -/
theorem arithmeticThirdInitialEquiv_third (b : Bool) :
    arithmeticThirdInitialEquiv hπ data H j hj u hu 3 b =
      arithmeticInitialBaseEquiv data H 3 j hj := by
  let t := parameter R π 3
  let I := ideal (Quotient R π 3) t
  let J := I.map (algebraMap (Quotient R π 3) (Quotient R π 3)[T;T⁻¹])
  let a := correctionPunctureFactor R π 3
    (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3) (V b) true
  let c := arithmeticInitialBaseEquiv data H 3 j hj
  have ha : ∀ z, a z - z ∈ J ^ 3 := by
    intro z
    dsimp only [a]
    rw [arithmeticThirdEarlierPuncture_third]
    exact LaurentReciprocalErrorConjugation.subst_sub_mem t 3
      (nextCorrectionParameter_square R π 2) _ z
  have hJ : J ^ (1 + 3) = ⊥ := by
    change ((Ideal.span {t}).map (algebraMap _ _)) ^ 4 = ⊥
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow R π 3,
      Ideal.span_singleton_zero, Ideal.map_bot]
  have hc := LaurentReciprocalErrorConjugation.conjugation_eq I 3 c.symm a.toAlgHom
    (arithmeticInitialBaseEquiv_symm_sub_mem data H 3 j hj) ha hJ
  apply AlgEquiv.ext
  intro z
  have hf := congrArg (fun e : (Quotient R π 3)[T;T⁻¹] ≃ₐ[Quotient R π 3]
      (Quotient R π 3)[T;T⁻¹] ↦ e (invert z))
    (arithmeticThirdPreceding_factorization hπ data H j hj u hu b)
  simp only [arithmeticThirdPrecedingEdgeEquiv, arithmeticSecondPrecedingIncomingEquiv,
    AlgEquiv.trans_apply, involutive_invert z] at hf
  have hh := congrArg invert hf
  rw [involutive_invert, involutive_invert] at hh
  have h := DFunLike.congr_fun hc z
  change c.symm (a (c z)) = invert (a (invert z)) at h
  rw [← hh] at h
  have he := congrArg c h
  rw [AlgEquiv.apply_symm_apply] at he
  change a.symm (c (arithmeticSecondPrecedingOpposite hπ data H 3 j hj u hu b
    (twoBranchCorrectionPunctureFactor R π 3
      (arithmeticSecondPrecedingSmoothing hπ data H 3 j hj u hu b) (P b) false z))) = c z
  rw [← he, AlgEquiv.symm_apply_apply]

end FLT.Mazur.WeierstrassDividedDepth
