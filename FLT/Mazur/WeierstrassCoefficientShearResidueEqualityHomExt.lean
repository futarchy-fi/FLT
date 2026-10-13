/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueEquality
public import FLT.Mazur.WeierstrassCoefficientShearRootEqualityHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueBranchCharts
public import FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Full residue components detect the original terminal charts

The actual equality component determines the entire divided chart and the last
retained conic. The last branch pair then determines the full final retained chart.
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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)

variable (hstart : 0 < start)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + s from by omega)
local notation "C" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6 hc
local notation "conic" => coefficientShearRetainedConic hπ data Q r (s + 1) hs
  ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2 hr

/-- The actual equality component determines the entire last conic. -/
theorem coefficientShearResidueEqualityConic_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (h : C ≫ u = C ≫ v) : conic ≫ u = conic ≫ v := by
  unfold coefficientShearResidueEqualityComponent at h
  rw [dite_eq_left (show 0 < start + s from by omega)] at h
  exact coefficientShearRootEqualityConic_hom_ext
    hπ data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha u v h

include hstart in
/-- The actual equality component detects the entire divided equation at the final stage. -/
theorem coefficientShearResidueEqualityDividedChart_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (h : C ≫ u = C ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 1) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 1) ≫ v := by
  unfold coefficientShearResidueEqualityComponent at h
  rw [dite_eq_left (show 0 < start + s from by omega)] at h
  exact coefficientShearRootEqualityDividedChart_hom_ext
    hπ data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha u v h

variable (h6mem : W.a₆ ∈ maximalIdeal R ^ depth)
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 h6mem hc
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

/-- The final complete branch pair and equality component determine the last retained chart. -/
theorem coefficientShearResidueLastRetainedChart_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (hB : ∀ i, B ⟨s, Nat.lt_succ_self s⟩ i ≫ u = B ⟨s, Nat.lt_succ_self s⟩ i ≫ v)
    (hC : C ≫ u = C ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr ⟨s, Nat.lt_succ_self s⟩) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr ⟨s, Nat.lt_succ_self s⟩) ≫ v := by
  apply coefficientShearRetainedChart_hom_ext hπ data Q r (s + 1) hs ⟨s, Nat.lt_succ_self s⟩
    hscale hp (lin).1 (lin).2 hr hu
  · exact coefficientShearResidueEqualityConic_hom_ext
      hπ hm data s hs he h3 h4 h6 hc hstart u v hC
  · have H := coefficientShearResidueRetainedPair_hom_ext
      hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 h6mem hc u v
      ⟨s, Nat.lt_succ_self s⟩ 0 (hB 0)
    simpa only [coefficientShearResidueRetainedPair, ite_true] using H
  · have H := coefficientShearResidueRetainedPair_hom_ext
      hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 h6mem hc u v
      ⟨s, Nat.lt_succ_self s⟩ 1 (hB 1)
    simpa only [coefficientShearResidueRetainedPair, Fin.ext_iff, Fin.val_zero,
      Fin.val_one, Nat.one_ne_zero, ↓reduceIte] using H

end FLT.Mazur.WeierstrassDividedDepth
