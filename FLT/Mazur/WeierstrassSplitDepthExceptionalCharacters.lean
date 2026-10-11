/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthConormal
public import FLT.Mazur.RegularCenterResidueConormal

/-!
# Actual exceptional quotient characters at split depth

The integral ordinary addition formulas induce reciprocal balanced characters
on a regular principalization of the original center, after residue restriction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open IsLocalRing WeierstrassDividedDepth RegularCenter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S B C : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [CommRing B] [CommRing C]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (d : Data W π k) (hk : 2 * k ≤ depth)
  (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
local notation "I" => Ideal.map
  (AlgHom.toRingHom (AlgHom.comp f (ordinaryInputRight W b)))
  (modificationChartCenter W (π ^ k) 2)
local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "a" => algebraMap R S W.a₁
local notation "x" => f (ordinaryInputRight W b (coord W 2 0))
local notation "y" => f (ordinaryInputRight W b (coord W 2 1))
local notation "X" => f (ordinaryChartAddition W b (coord W 2 0))
local notation "Y" => f (ordinaryChartAddition W b (coord W 2 1))
local notation "l" => f (ordinaryChartSlope W b)

omit [IsDomain R] [IsLocalRing R] in
include d in
/-- Both input and output coordinate pairs belong to the actual original center. -/
theorem splitDepthExceptional_coordinates_mem : (x ∈ I ∧ y ∈ I) ∧ (X ∈ I ∧ Y ∈ I) := by
  constructor
  · rw [modificationChartCenter_map]
    exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  · rw [modificationChartCenter_map]
    exact ordinarySpecialization_modificationCenter W b f (π ^ k) d.b3 d.b4
      d.factor3 d.factor4

local notation "H" => splitDepthExceptional_coordinates_mem d b f
variable (φ : S →+* B) (z : B) (hI : ((modificationChartCenter W (π ^ k) 2).map
    (f.comp (ordinaryInputRight W b)).toRingHom).map φ = Ideal.span {z}) (hz : IsRegular z)
  (ψ : B →+* C) (hψ : ψ z = 0) (hJ : (maximalIdeal R).map (algebraMap R S) ≤ RingHom.ker (ψ.comp φ))

include D hk hz hψ hJ in
/-- The original first branch character acts on the actual regular-center quotients. -/
theorem splitDepthExceptional_first_character :
    ψ (φ l) * ψ (quotient I φ z hI Y (H).2.2) =
      ψ (φ (l + a)) * ψ (quotient I φ z hI y (H).1.2) :=
  quotient_residue_balanced_character I J φ z hI hz ψ hψ hJ
    Y y l (l + a) (H).2.2 (H).1.2 (splitDepthConormal_characters D d hk b f).1

include D hk hz hψ hJ in
/-- The opposite original branch has the reciprocal balanced quotient character. -/
theorem splitDepthExceptional_second_character :
    ψ (φ (l + a)) * ψ (quotient I φ z hI (Y + a * X)
      ((I).add_mem (H).2.2 ((I).mul_mem_left a (H).2.1))) =
    ψ (φ l) * ψ (quotient I φ z hI (y + a * x)
      ((I).add_mem (H).1.2 ((I).mul_mem_left a (H).1.1))) :=
  quotient_residue_balanced_character I J φ z hI hz ψ hψ hJ
    (Y + a * X) (y + a * x) (l + a) l _ _
    (splitDepthConormal_characters D d hk b f).2

end FLT.Mazur.WeierstrassIntegralChart
