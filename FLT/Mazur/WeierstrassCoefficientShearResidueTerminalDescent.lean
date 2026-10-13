/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityDescent
public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.PolygonCyclicPushout
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityDescent

/-!
# Cyclic descent to the final retained and divided residue equations

The completed equality component supplies its full conic with the original nonzero constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
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

variable (hstart : 0 < start)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + s from by omega)

local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "q" => coefficientShearEqualityConicParameter
  data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha
local notation "I" => coefficientShearRetainedEquationIso data Q r (s + 1) hs
  ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2
local notation "ρ" => ProjectiveLine.endpointReversal Q
variable {Y : Scheme}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫ F i =
      ProjectiveLine.infinity (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫
        F (PolygonPinching.next (by omega) i))

/-- The cyclic cocone descends to the full final retained equation at equality depth. -/
@[irreducible] def coefficientShearResidueLastDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs
      (.inr ⟨s, Nat.lt_succ_self s⟩) ⟶ Y :=
  coefficientShearRetainedEqualityDesc data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha
    (ρ ≫ F ⟨s + 2, by omega⟩) (ρ ≫ F ⟨s + 1, by omega⟩) (F ⟨s + 3, by omega⟩)
    (by
      rw [ProjectiveLine.zero_endpointReversal_assoc,
        ProjectiveLine.infinity_endpointReversal_assoc]
      have hn : PolygonPinching.next (by omega) (⟨s + 1, by omega⟩ : Fin (2 * s + 4)) =
          ⟨s + 2, by omega⟩ := by
        apply Fin.ext
        change (s + 1 + 1) % (2 * s + 4) = s + 2
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn] using (w ⟨s + 1, by omega⟩).symm)
    (by
      rw [ProjectiveLine.infinity_endpointReversal_assoc]
      have hn : PolygonPinching.next (by omega) (⟨s + 2, by omega⟩ : Fin (2 * s + 4)) =
          ⟨s + 3, by omega⟩ := by
        apply Fin.ext
        change (s + 2 + 1) % (2 * s + 4) = s + 3
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn] using w ⟨s + 2, by omega⟩)
local notation "D" => coefficientShearResidueLastDesc
  hπ hm data s hs he h3 h4 h6 hc hstart F w

/-- The whole final conic receives the correctly reversed actual equality component. -/
theorem coefficientShearResidueLastDesc_conic :
    middleConicImmersion U c h2 ≫ (I).hom ≫ D = q ≫ ρ ≫ F ⟨s + 2, by omega⟩ := by
  rw [coefficientShearResidueLastDesc]
  erw [coefficientShearRetainedEqualityDesc_conic]

/-- The complete first line keeps its positive tangent scale and first branch position. -/
theorem coefficientShearResidueLastDesc_first :
    middleLineImmersion U c h2 0 (middle_first_root U) ≫ (I).hom ≫ D =
      ProjectiveLine.chartScaling Q a ≫ ProjectiveLine.left Q ≫ F ⟨s + 1, by omega⟩ := by
  rw [coefficientShearResidueLastDesc]
  erw [coefficientShearRetainedEqualityDesc_first, ProjectiveLine.right_endpointReversal_assoc]

/-- The complete opposite line keeps its negative tangent scale and opposite branch position. -/
theorem coefficientShearResidueLastDesc_second :
    middleLineImmersion U c h2 (-(U).a₁) (middle_second_root U) ≫ (I).hom ≫ D =
      ProjectiveLine.chartScaling Q (-a) ≫ ProjectiveLine.right Q ≫ F ⟨s + 3, by omega⟩ := by
  rw [coefficientShearResidueLastDesc]
  erw [coefficientShearRetainedEqualityDesc_second]

/-- The same completed equality component supplies the entire actual divided atlas equation. -/
@[irreducible] def coefficientShearResidueDividedDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 1) ⟶ Y :=
  coefficientShearEqualityDividedParameter data Q r s hs hp (lin).1 (lin).2 cunit hr a ha ≫
    ρ ≫ F ⟨s + 2, by omega⟩

end FLT.Mazur.WeierstrassDividedDepth
