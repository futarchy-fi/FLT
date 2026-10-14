/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueBranchCharts
public import FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# The final strict positive-start retained equation is detected by four components

The original previous pair determines the lines and the terminal pair determines the conic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm e hk h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
open WeierstrassModificationX
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (e).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "Z" => conicZeroAffineIso c g6
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc

variable (hstart : 0 < start)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + s from by omega)
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc

/-- Both whole terminal components and the preceding pair detect the last retained equation. -/
theorem coefficientShearResidueStrictLastRetainedChart_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (hB : ∀ i, B ⟨s, Nat.lt_succ_self s⟩ i ≫ u = B ⟨s, Nat.lt_succ_self s⟩ i ≫ v)
    (hT : ∀ i, T i ≫ u = T i ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr ⟨s, Nat.lt_succ_self s⟩) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr ⟨s, Nat.lt_succ_self s⟩) ≫ v := by
  apply coefficientShearRetainedChart_hom_ext hπ data Q r (s + 1) hs ⟨s, Nat.lt_succ_self s⟩
    hscale hp (lin).1 (lin).2 hr hu
  · exact coefficientShearResidueStrictPositiveConic_hom_ext
      hπ hm data s hs hk h3 h4 h6 hc (by omega) u v (hT 0) (hT 1)
  · have H := coefficientShearResidueRetainedPair_hom_ext
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc u v
      ⟨s, Nat.lt_succ_self s⟩ 0 (hB 0)
    simpa only [coefficientShearResidueRetainedPair, ite_true] using H
  · have H := coefficientShearResidueRetainedPair_hom_ext
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc u v
      ⟨s, Nat.lt_succ_self s⟩ 1 (hB 1)
    simpa only [coefficientShearResidueRetainedPair, Fin.ext_iff, Fin.val_zero,
      Fin.val_one, Nat.one_ne_zero, ↓reduceIte] using H

end FLT.Mazur.WeierstrassDividedDepth
