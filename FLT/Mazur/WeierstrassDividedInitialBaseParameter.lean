/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialRightParameter
public import FLT.Mazur.WeierstrassModificationXArithmeticMobiusParameterAlgebra

/-!
# The original full initial edge parameter and its coefficient reduction

The base parameter combines the inverse original Mobius map with the full
right coordinate of the first retained node. It reduces to inversion only
modulo the coefficient ideal, while the complete isomorphism is retained.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "K" => Ideal.map (algebraMap Q L) (ideal Q (parameter R π m))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "M" => arithmeticInitialMobiusEquiv π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "B" => arithmeticInitialRightEquiv data H m j hj

/-- The entire original initial-edge base substitution, in contravariant algebra order. -/
def arithmeticInitialBaseEquiv : L ≃ₐ[Q] L := (B).trans (M).symm

local notation "E" => arithmeticInitialBaseEquiv data H m j hj

/-- Its inverse preserves the exact reciprocal coefficient reduction on every Laurent value. -/
theorem arithmeticInitialBaseEquiv_symm_sub_mem (z : L) :
    (E).symm z - invert z ∈ K := by
  have hb := arithmeticInitialRightEquiv_symm_sub_mem data H m j hj (M z)
  have hm := arithmeticInitialMobiusEquiv_sub_mem π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) z
  change (B).symm (M z) - invert z ∈ K
  simpa only [sub_add_sub_cancel] using (K).add_mem hb hm

/-- The complete forward parameter has the same reciprocal reduction. -/
theorem arithmeticInitialBaseEquiv_sub_mem (z : L) : E z - invert z ∈ K := by
  have h := (K).neg_mem
    (arithmeticInitialBaseEquiv_symm_sub_mem data H m j hj (E z))
  rw [AlgEquiv.symm_apply_apply, neg_sub] at h
  have hi : K ≤ Ideal.comap invert.toAlgHom.toRingHom K := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change invert (algebraMap Q L x) ∈ K
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hx
  have hh := hi h
  change invert (invert (E z) - z) ∈ K at hh
  rw [map_sub, involutive_invert (E z)] at hh
  exact hh

/-- The full base parameter is exactly the original Mobius/right composite in the atlas. -/
theorem arithmeticInitialBaseEquiv_spec :
    (punctureSpecIso E).hom =
      (arithmeticInitialMobiusParameter π m W (π ^ 1)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
          (H.b3_div _) (H.b4_div _) (H.b6_div _)).inv ≫
        arithmeticRetainedRightParameter data H m j hj ⟨0, Nat.zero_lt_succ j⟩ := by
  rw [arithmeticInitialBaseEquiv, punctureSpecIso_trans]
  change (punctureSpecIso M).inv ≫ (punctureSpecIso B).hom = _
  rw [arithmeticInitialMobiusEquiv_spec, arithmeticInitialRightEquiv_spec]

end FLT.Mazur.WeierstrassDividedDepth
