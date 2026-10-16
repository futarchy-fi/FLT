/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapRatio

/-!
# Explicit evaluation on the original opposite node intersection

The reflected original denominator is invertible on the full D(q) overlap.
Localization followed by the inverse opposite-node equivalence constructs
its actual ring map, retaining every nilpotent correction.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "O'" => PolynomialOppositeInitialOpen W s b3 b4 b6 r
local notation "Q" => algebraMap N L (NodalFiber.q s)
local notation "D" => polynomialOppositeDenominator W s b3 b4 b6 r
local notation "E" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3

/-- The full reflected denominator is a nilpotent perturbation of the unit -q. -/
theorem polynomialNodeOverlap_oppositeDenominator_isUnit : IsUnit (G D) := by
  have hn := NilpotentQuadraticRoot.element_nilpotent (I.map (algebraMap R L))
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R L))
    (polynomialNodeForwardBase_oppositeDenominator_mem W s b3 b4 b6 r hr I hI hrI h3)
  have hm := hn.map (algebraMap L O)
  have hq : IsUnit (algebraMap L O Q) := IsLocalization.Away.algebraMap_isUnit Q
  have hu := hm.isUnit_add_left_of_commute hq.neg (mul_comm _ _)
  change IsUnit (algebraMap L O (E D))
  convert hu using 1
  rw [map_add]
  ring

/-- Extend the original full overlap evaluation to the original opposite principal open. -/
def polynomialNodeOverlapOppositeLift : O' →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom D (f := G)
    (polynomialNodeOverlap_oppositeDenominator_isUnit W s b3 b4 b6 r hr I hI hrI h3)

/-- Extension preserves every function of the original initial affine scheme. -/
theorem polynomialNodeOverlapOppositeLift_base (z : A) :
    polynomialNodeOverlapOppositeLift W s b3 b4 b6 r hr I hI hrI h3
      (algebraMap A O' z) = G z := by
  rw [polynomialNodeOverlapOppositeLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The ring map to the actual opposite full node on their entire original intersection. -/
def polynomialNodeOverlapOppositeEvaluation : L →ₐ[R] O :=
  (polynomialNodeOverlapOppositeLift W s b3 b4 b6 r hr I hI hrI h3).comp
    (polynomialOppositeNodeEquiv W s b3 b4 b6 r hr I hI hrI h3).symm.toAlgHom

/-- The explicit opposite restriction agrees with every original affine function. -/
theorem polynomialNodeOverlapOppositeEvaluation_global (z : A) :
    polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3
      (E (initialReflection W s b3 b4 b6 z)) = G z := by
  rw [← polynomialOppositeNodeEquiv_base W s b3 b4 b6 r hr I hI hrI h3 z]
  simp only [polynomialNodeOverlapOppositeEvaluation, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  exact polynomialNodeOverlapOppositeLift_base W s b3 b4 b6 r hr I hI hrI h3 z

/-- The explicit ring map is exactly the pre-existing geometric opposite restriction. -/
theorem polynomialNodeOverlapOpposite_eq_spec :
    polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 =
      Spec.map (CommRingCat.ofHom
        (polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3).toRingHom) := by
  apply (cancel_mono (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3)).mp
  rw [polynomialNodeOverlapOpposite_global, polynomialNodeOverlapEvaluation_spec,
    polynomialOppositeNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (polynomialNodeOverlapOppositeEvaluation_global W s b3 b4 b6 r hr I hI hrI h3 z).symm

end FLT.Mazur.WeierstrassModificationX
