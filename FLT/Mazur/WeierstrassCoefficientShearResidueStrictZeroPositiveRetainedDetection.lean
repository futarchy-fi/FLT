/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentPositiveDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentLineDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
public import FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt

/-!
# Complete original components detect every positive retained chart

The full adjacent conic or strict terminal pair and preceding adjacent pair
jointly determine the entire original retained equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hle" => Nat.le_of_lt hk
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hle h3 h4 hc
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

open WeierstrassModificationX WeierstrassSuccessiveX
variable {Y : Scheme} (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)
  (i : Fin (s + 1)) (hipos : 0 < i.val)
local notation "e" => data ⟨i.val + 1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e
  (show 2 * (0 + (i.val + 1)) ≤ depth from by omega) h3 h4
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < 0 + i.val from by omega)
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

include hipos in
/-- Every positive retained chart is determined by the full original component family. -/
theorem coefficientShearResidueStrictZeroPositiveRetained_hom_ext
    (hB : ∀ j k, B j k ≫ u = B j k ≫ v) (hT : ∀ k, T k ≫ u = T k ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr i) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr i) ≫ v := by
  apply coefficientShearRetainedChart_hom_ext hπ data Q r (s + 1) hs i
    hscale hp (lin).1 (lin).2 hr hu
  · by_cases hilast : i.val = s
    · have hi' : i = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hilast
      subst i
      exact coefficientShearResidueStrictPositiveConic_hom_ext
        hπ hm data s hs hk h3 h4 h6 hc (by omega) u v (hT 0) (hT 1)
    · let j : Fin s := ⟨i.val, by omega⟩
      exact coefficientShearResidueAdjacentPositiveConic_hom_ext
        hπ hm data s hs hle h3 h4 hc j (by dsimp [j]; omega) u v (hB j 0) (hB j 1)
  · let prev : Fin s := ⟨i.val - 1, by omega⟩
    have hi : prev.succ = i := Fin.ext (by dsimp [prev]; omega)
    simpa only [← hi] using coefficientShearResidueAdjacentFirstLine_hom_ext
      hπ hm data s hs hle h3 h4 hc prev u v (hB prev 0)
  · let prev : Fin s := ⟨i.val - 1, by omega⟩
    have hi : prev.succ = i := Fin.ext (by dsimp [prev]; omega)
    simpa only [← hi] using coefficientShearResidueAdjacentSecondLine_hom_ext
      hπ hm data s hs hle h3 h4 hc prev u v (hB prev 1)

end FLT.Mazur.WeierstrassDividedDepth
