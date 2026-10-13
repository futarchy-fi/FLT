/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent
public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentLine
public import FLT.Mazur.PolygonCyclicPushout
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent

/-!
# The start-zero cyclic family descends to positive interior equations

Both branch reversals and the original signed tangent scales are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄) (j : Fin s)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "hj" => show j.val + 1 ≤ n from by omega
local notation "hjNext" => show j.val + 2 ≤ n from by omega
local notation "e" => data ⟨j.val + 2, Nat.lt_succ_of_le hjNext⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

variable (hjpos : 0 < j.val)

local notation "d" => data ⟨j.val + 1, Nat.lt_succ_of_le hj⟩
local notation "gc" => coefficientShearAdjacent_coefficients hπ d e Q hp
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < 0 + j.val from by omega)
local notation "Z" => conicZeroAffineIso c (gc).2.2

local notation "I" => coefficientShearRetainedEquationIso data Q r (s + 1) hs
  j.castSucc hscale hp (gc).1 (gc).2.1
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "p₁" => (conicFirstParameterIso (U).a₁ c hu).inv ≫
  conicFirstOpenImmersion (U).a₁ c
local notation "p₂" => (conicSecondParameterIso (U).a₁ c hu).inv ≫
  conicSecondOpenImmersion (U).a₁ c
local notation "ρ" => ProjectiveLine.endpointReversal Q
variable {Y : Scheme}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫ F i =
      ProjectiveLine.infinity (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫
        F (PolygonPinching.next (by omega) i))

/-- The actual cyclic family descends to the entire nonterminal retained equation. -/
@[irreducible] def coefficientShearResidueZeroInteriorDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inr j.castSucc) ⟶ Y :=
  coefficientShearRetainedZeroDesc data Q r (s + 1) hs j.castSucc
    hscale hp (gc).1 (gc).2.1 hr hu (gc).2.2 a (-a)
    (ρ ≫ F ⟨j.val + 1, by omega⟩) (F ⟨2 * s + 1 - j.val, by omega⟩)
    (ρ ≫ F ⟨j.val, by omega⟩) (F ⟨2 * s + 2 - j.val, by omega⟩)
    (by
      rw [ProjectiveLine.zero_endpointReversal_assoc,
        ProjectiveLine.infinity_endpointReversal_assoc]
      have hn : PolygonPinching.next (by omega) (⟨j.val, by omega⟩ : Fin (2 * s + 2)) =
          ⟨j.val + 1, by omega⟩ := by
        apply Fin.ext
        change (j.val + 1) % (2 * s + 2) = j.val + 1
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn] using (w ⟨j.val, by omega⟩).symm)
    (by
      have hn : PolygonPinching.next (by omega)
          (⟨2 * s + 1 - j.val, by omega⟩ : Fin (2 * s + 2)) =
            ⟨2 * s + 2 - j.val, by omega⟩ := by
        apply Fin.ext
        change (2 * s + 1 - j.val + 1) % (2 * s + 2) = 2 * s + 2 - j.val
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      simpa only [hn] using w ⟨2 * s + 1 - j.val, by omega⟩)
local notation "D" => coefficientShearResidueZeroInteriorDesc
  hπ hm data s hs h3 h4 hc j hjpos F w

/-- The first complete conic branch is the right chart at its actual cyclic position. -/
theorem coefficientShearResidueZeroInteriorDesc_first_conic :
    (Z).hom ≫ p₁ ≫ middleConicImmersion U c h2 ≫ (I).hom ≫ D =
      ProjectiveLine.right Q ≫ F ⟨j.val + 1, by omega⟩ := by
  rw [coefficientShearResidueZeroInteriorDesc]
  erw [(coefficientShearRetainedZeroDesc_first_conic
      data Q r (s + 1) hs j.castSucc hscale hp (gc).1 (gc).2.1 hr hu),
    ProjectiveLine.left_endpointReversal_assoc]

/-- The opposite complete conic branch retains its original left chart. -/
theorem coefficientShearResidueZeroInteriorDesc_second_conic :
    (Z).hom ≫ p₂ ≫ middleConicImmersion U c h2 ≫ (I).hom ≫ D =
      ProjectiveLine.left Q ≫ F ⟨2 * s + 1 - j.val, by omega⟩ := by
  rw [coefficientShearResidueZeroInteriorDesc]
  erw [(coefficientShearRetainedZeroDesc_second_conic
      data Q r (s + 1) hs j.castSucc hscale hp (gc).1 (gc).2.1 hr hu)]

/-- The entire first horizontal line carries its original positive tangent scale. -/
theorem coefficientShearResidueZeroInteriorDesc_first_line :
    middleLineImmersion U c h2 0 (middle_first_root U) ≫ (I).hom ≫ D =
      ProjectiveLine.chartScaling Q a ≫ ProjectiveLine.left Q ≫
        F ⟨j.val, by omega⟩ := by
  rw [coefficientShearResidueZeroInteriorDesc]
  erw [(coefficientShearRetainedZeroDesc_first_line
      data Q r (s + 1) hs j.castSucc hscale hp (gc).1 (gc).2.1 hr hu),
    ProjectiveLine.right_endpointReversal_assoc]

/-- The entire opposite line carries the original negative tangent scale. -/
theorem coefficientShearResidueZeroInteriorDesc_second_line :
    middleLineImmersion U c h2 (-(U).a₁) (middle_second_root U) ≫ (I).hom ≫ D =
      ProjectiveLine.chartScaling Q (-a) ≫ ProjectiveLine.right Q ≫
        F ⟨2 * s + 2 - j.val, by omega⟩ := by
  rw [coefficientShearResidueZeroInteriorDesc]
  erw [(coefficientShearRetainedZeroDesc_second_line
      data Q r (s + 1) hs j.castSucc hscale hp (gc).1 (gc).2.1 hr hu)]

end FLT.Mazur.WeierstrassDividedDepth
