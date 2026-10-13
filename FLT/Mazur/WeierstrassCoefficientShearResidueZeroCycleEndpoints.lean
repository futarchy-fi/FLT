/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueEqualityPositiveEndpoints

/-!
# Every endpoint in the original start-zero equality cycle

The exterior, every adjacent pair and the original equality terminal satisfy
the cyclic endpoint equations, including the two-component case.
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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- Every original cyclic zero equals infinity on the actual next complete component. -/
theorem coefficientShearResidueZeroEqualityCycleComponent_endpoints
    (i : Fin (2 * s + 2)) :
    ProjectiveLine.zero Q ≫ C i =
      ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) := by
  have hn (hi : i.val + 1 < 2 * s + 2) :
      PolygonPinching.next (by omega) i = (⟨i.val + 1, hi⟩ : Fin (2 * s + 2)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  by_cases hs0 : s = 0
  · subst s
    fin_cases i
    · change ProjectiveLine.zero Q ≫
        coefficientShearResidueZeroEqualityCycleComponent
          hπ hm data 0 hs he h3 h4 h6next hc 0 =
          ProjectiveLine.infinity Q ≫ coefficientShearResidueZeroEqualityCycleComponent
            hπ hm data 0 hs he h3 h4 h6next hc ⟨0 + 1, by omega⟩
      rw [coefficientShearResidueZeroEqualityCycleComponent_exterior,
        coefficientShearResidueZeroEqualityCycleComponent_terminal,
        ProjectiveLine.infinity_endpointReversal_assoc]
      exact (coefficientShearResidueZeroEquality_first
        hπ hm data hs he h3 h4 h6next hc).symm
    · change ProjectiveLine.zero Q ≫
        coefficientShearResidueZeroEqualityCycleComponent
          hπ hm data 0 hs he h3 h4 h6next hc ⟨0 + 1, by omega⟩ =
          ProjectiveLine.infinity Q ≫ coefficientShearResidueZeroEqualityCycleComponent
            hπ hm data 0 hs he h3 h4 h6next hc 0
      rw [coefficientShearResidueZeroEqualityCycleComponent_exterior,
        coefficientShearResidueZeroEqualityCycleComponent_terminal,
        ProjectiveLine.zero_endpointReversal_assoc]
      exact coefficientShearResidueZeroEquality_second hπ hm data hs he h3 h4 h6next hc
  have hspos : 0 < s := by omega
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    rw [hn (by omega), coefficientShearResidueZeroEqualityCycleComponent_exterior]
    change ProjectiveLine.zero Q ≫ F = ProjectiveLine.infinity Q ≫
      C ⟨(⟨0, hspos⟩ : Fin s).val + 1, by omega⟩
    rw [coefficientShearResidueZeroEqualityCycleComponent_first,
      ProjectiveLine.infinity_endpointReversal_assoc]
    exact (coefficientShearResidueZeroAdjacent_first
      hπ hm data s hs hk h3 h4 hc hspos).symm
  by_cases hi1 : i.val < s
  · let j : Fin s := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 2)) =
        ⟨(⟨j.val + 1, by dsimp [j]; omega⟩ : Fin s).val + 1, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueZeroEqualityCycleComponent_first,
      coefficientShearResidueZeroEqualityCycleComponent_first,
      ProjectiveLine.zero_endpointReversal_assoc, ProjectiveLine.infinity_endpointReversal_assoc]
    exact coefficientShearResidueAdjacentComponent_join
      hπ hm data s hs he h3 h4 hc j (by dsimp [j]; omega) 0
  by_cases hi2 : i.val = s
  · have hi : i = ⟨(⟨s - 1, by omega⟩ : Fin s).val + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 2)) =
        ⟨s + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueZeroEqualityCycleComponent_first,
      coefficientShearResidueZeroEqualityCycleComponent_terminal,
      ProjectiveLine.zero_endpointReversal_assoc, ProjectiveLine.infinity_endpointReversal_assoc]
    exact coefficientShearResidueAdjacentComponent_equality_first
      hπ hm data s hs he h3 h4 h6next hc hspos
  by_cases hi3 : i.val = s + 1
  · have hi : i = ⟨s + 1, by omega⟩ := Fin.ext hi3
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 2)) =
        ⟨2 * s + 1 - (⟨s - 1, by omega⟩ : Fin s).val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueZeroEqualityCycleComponent_terminal,
      coefficientShearResidueZeroEqualityCycleComponent_second,
      ProjectiveLine.zero_endpointReversal_assoc]
    exact (coefficientShearResidueAdjacentComponent_equality_second
      hπ hm data s hs he h3 h4 h6next hc hspos).symm
  by_cases hil : i.val = 2 * s + 1
  · have hi : i = ⟨2 * s + 1 - (⟨0, hspos⟩ : Fin s).val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    have hnext : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 2)) := by
      apply Fin.ext
      change (i.val + 1) % (2 * s + 2) = 0
      rw [show i.val + 1 = 2 * s + 2 by omega, Nat.mod_self]
    rw [hnext, hi, coefficientShearResidueZeroEqualityCycleComponent_second,
      coefficientShearResidueZeroEqualityCycleComponent_exterior]
    exact coefficientShearResidueZeroAdjacent_second hπ hm data s hs hk h3 h4 hc hspos
  · let j : Fin s := ⟨2 * s - i.val, by omega⟩
    have hi : i = ⟨2 * s + 1 - (⟨j.val + 1, by dsimp [j]; omega⟩ : Fin s).val,
        by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 2)) =
        ⟨2 * s + 1 - j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueZeroEqualityCycleComponent_second,
      coefficientShearResidueZeroEqualityCycleComponent_second]
    exact (coefficientShearResidueAdjacentComponent_join
      hπ hm data s hs he h3 h4 hc j (by dsimp [j]; omega) 1).symm

end FLT.Mazur.WeierstrassDividedDepth
