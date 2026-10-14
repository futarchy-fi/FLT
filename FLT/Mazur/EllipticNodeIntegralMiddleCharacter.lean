/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeIntegralOppositeCharacter
public import FLT.Mazur.EllipticNodeMiddleCharacterAlgebra

/-!
# The smooth character of an integral middle-depth sum

The second slope identity determines the character of the actual smooth
reduction, including the doubling chart.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [DecidableEq (ResidueField A)]

/-- An arbitrary smooth reduced point of the actual sum has the middle-depth character. -/
theorem node_integral_middle_reduction_character (k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (a b c d l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (hb : IsUnit b) (hd : IsUnit (d + W.a₁ * c))
    (hxy : ¬ (((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
      ((π ^ k * b : A) : K) ((π ^ k * d : A) : K) = (l : K))
    (q : (W.map (residue A)).toAffine.Point)
    (hq : ReducesTo A W (.some _ _ h₁ + .some _ _ h₂) q) :
    residue A b * (Additive.toMul (splitDepthResidueCharacter D q)).val =
      -residue A (d + W.a₁ * c) := by
  obtain ⟨e₃, he₃, h3⟩ := exists_node_deep_factor D.maximalIdeal_eq k
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨e₄, he₄, h4⟩ := exists_node_deep_factor D.maximalIdeal_eq k
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  have hπm : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hr := node_equal_depth_second_residue A W D.uniformizer_ne_zero hπm k hk
    a b c d l e₃ e₄ D.a₂_mem he₃ he₄ h3 h4 h₁.1 h₂.1 hxy hl
  have ht := node_middle_slope_not_tangent W D.a₁_unit hb hd hr
  have hm (e : A) : π ^ k * e ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_right e
      (Ideal.pow_le_self (Nat.ne_of_gt hk) (Ideal.pow_mem_pow hπm k))
  rw [Affine.Point.add_some hxy] at hq
  simp only [hl] at hq
  have hx := W.toAffine.map_addX (algebraMap A K) (π ^ k * a) (π ^ k * c) l
  have hy := W.toAffine.map_addY (algebraMap A K) (π ^ k * a) (π ^ k * b) (π ^ k * c) l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hx
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hy
  simp only [ValuationSubring.algebraMap_apply] at hx hy
  simp only [hx, hy] at hq
  have hs := (smoothReduction_affine_iff A W _ _ _).mp
    ((exists_reducesTo_iff A W _).mp ⟨q, hq⟩)
  have he := hq.unique A W (reducesTo_integral A W _ _ _ hs)
  rw [he, splitDepthResidueCharacter_node_add D _ _ _ l (hm a) (hm b) (hm c) ht hs]
  exact node_middle_slope_character W D.a₁_unit hb hd hr


end FLT.Mazur
