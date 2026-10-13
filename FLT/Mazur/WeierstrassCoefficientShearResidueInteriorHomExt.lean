/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentLeftCharts
public import FLT.Mazur.WeierstrassCoefficientShearResidueBranchCharts
public import FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Complete residue components determine each nonterminal retained chart

The next full pair determines the conic through its two entire parameter charts.
The pair at the current level determines both horizontal lines, hence the chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄) (j : Fin s)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "hj" => show j.val + 1 ≤ n from by omega
local notation "hjNext" => show j.val + 2 ≤ n from by omega
local notation "m" => s - (j.val + 1)
local notation "hs'" => show j.val + 2 + m ≤ n from by omega
local notation "e" => data ⟨j.val + 2, Nat.lt_succ_of_le hjNext⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "E" => coefficientShearStageIso hπ data Q r
  (j.val + 2 + m) (s + 1) hs' hs (by omega)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

variable (hstart : 0 < start)
local notation "C" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j
local notation "N" => coefficientShearResidueRetainedNode
  hπ hm data s hs hk hstart h3 h4

local notation "d" => data ⟨j.val + 1, Nat.lt_succ_of_le hj⟩
local notation "gc" => coefficientShearAdjacent_coefficients hπ d e Q hp
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + j.val from by omega)
local notation "conic" => coefficientShearRetainedConic hπ data Q r (s + 1) hs
  j.castSucc hscale hp (gc).1 (gc).2.1 hr
local notation "Z" => conicZeroAffineIso c (gc).2.2

/-- The complete adjacent pair detects maps on the whole preceding retained conic. -/
theorem coefficientShearResidueAdjacentConic_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (h₁ : C 0 ≫ u = C 0 ≫ v) (h₂ : C 1 ≫ u = C 1 ≫ v) :
    conic ≫ u = conic ≫ v := by
  apply conicParameter_hom_ext (U).a₁ c hu
  · have h := congrArg (fun k => ProjectiveLine.left Q ≫ k) h₁
    rw [coefficientShearResidueAdjacentComponent_first_left_assoc (hstart := hstart),
      coefficientShearResidueAdjacentComponent_first_left_assoc (hstart := hstart)] at h
    apply (cancel_epi (Z).hom).mp
    simpa only [coefficientConicFirstParameter, Category.assoc] using h
  · have h := congrArg (fun k => ProjectiveLine.left Q ≫ k) h₂
    rw [coefficientShearResidueAdjacentComponent_second_left_assoc (hstart := hstart),
      coefficientShearResidueAdjacentComponent_second_left_assoc (hstart := hstart)] at h
    apply (cancel_epi (Z).hom).mp
    simpa only [coefficientConicSecondParameter, Category.assoc] using h

variable (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Consecutive complete branch pairs determine the entire original retained chart. -/
theorem coefficientShearResidueInteriorChart_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (hprev : ∀ i, B j.castSucc i ≫ u = B j.castSucc i ≫ v)
    (hnext : ∀ i, B j.succ i ≫ u = B j.succ i ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr j.castSucc) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr j.castSucc) ≫ v := by
  apply coefficientShearRetainedChart_hom_ext hπ data Q r (s + 1) hs j.castSucc
    hscale hp (gc).1 (gc).2.1 hr hu
  · apply coefficientShearResidueAdjacentConic_hom_ext
      hπ hm data s hs hk h3 h4 hc j hstart
    · simpa only [Fin.succ, coefficientShearResidueBranchComponent_adjacent] using hnext 0
    · simpa only [Fin.succ, coefficientShearResidueBranchComponent_adjacent] using hnext 1
  · have H := coefficientShearResidueRetainedPair_hom_ext
      hπ hm data s hs hk hstart h3 h4 h6 hc u v j.castSucc 0 (hprev 0)
    simpa only [coefficientShearResidueRetainedPair, ite_true] using H
  · have H := coefficientShearResidueRetainedPair_hom_ext
      hπ hm data s hs hk hstart h3 h4 h6 hc u v j.castSucc 1 (hprev 1)
    simpa only [coefficientShearResidueRetainedPair, Fin.ext_iff, Fin.val_zero,
      Fin.val_one, Nat.one_ne_zero, ↓reduceIte] using H

end FLT.Mazur.WeierstrassDividedDepth
