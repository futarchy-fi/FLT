/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueBranchEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorJunctions

/-!
# All cyclic endpoints of the actual nonsplit residue component family

Both exterior junctions, every retained node, and the equality terminal obey
the original cyclic pinching convention as equalities of scheme morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- Every cyclic zero endpoint agrees with infinity on the actual next component. -/
theorem coefficientShearResidueCycleComponent_endpoints (i : Fin (2 * s + 4)) :
    ProjectiveLine.zero Q ≫ C i =
      ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) := by
  have hn (hi : i.val + 1 < 2 * s + 4) :
      PolygonPinching.next (by omega) i = (⟨i.val + 1, hi⟩ : Fin (2 * s + 4)) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    rw [hn (by omega)]
    rw [coefficientShearResidueCycleComponent_exterior]
    change ProjectiveLine.zero Q ≫ F =
      ProjectiveLine.infinity Q ≫ C ⟨(0 : Fin (s + 1)).val + 1, by omega⟩
    rw [coefficientShearResidueCycleComponent_first,
      ProjectiveLine.infinity_endpointReversal_assoc,
      coefficientShearResidueBranchComponent_initial]
    exact coefficientShearResidueExterior_initial_first
      hπ hm data s hs hk hstart h3 h4 h6 hc
  by_cases hi1 : i.val ≤ s
  · let j : Fin s := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 4)) =
        ⟨j.succ.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    change ProjectiveLine.zero Q ≫ C ⟨j.castSucc.val + 1, by omega⟩ =
      ProjectiveLine.infinity Q ≫ C ⟨j.succ.val + 1, by omega⟩
    rw [coefficientShearResidueCycleComponent_first hπ hm data s hs he hstart h3 h4 h6 h6next hc
        j.castSucc,
      coefficientShearResidueCycleComponent_first,
      ProjectiveLine.zero_endpointReversal_assoc, ProjectiveLine.infinity_endpointReversal_assoc]
    exact coefficientShearResidueBranchComponent_endpoints
      hπ hm data s hs hk hstart h3 h4 h6 hc j 0
  by_cases hi2 : i.val = s + 1
  · have hi : i = ⟨(⟨s, by omega⟩ : Fin (s + 1)).val + 1, by omega⟩ := Fin.ext hi2
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 4)) =
        ⟨s + 2, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueCycleComponent_first,
      coefficientShearResidueCycleComponent_terminal,
      ProjectiveLine.zero_endpointReversal_assoc, ProjectiveLine.infinity_endpointReversal_assoc]
    exact coefficientShearResidueBranchComponent_terminal_first
      hπ hm data s hs hk hstart h3 h4 h6 hc he h6next
  by_cases hi3 : i.val = s + 2
  · have hi : i = ⟨s + 2, by omega⟩ := Fin.ext hi3
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 4)) =
        ⟨2 * s + 3 - (⟨s, by omega⟩ : Fin (s + 1)).val, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueCycleComponent_terminal,
      coefficientShearResidueCycleComponent_second, ProjectiveLine.zero_endpointReversal_assoc]
    exact (coefficientShearResidueBranchComponent_terminal_second
      hπ hm data s hs hk hstart h3 h4 h6 hc he h6next).symm
  by_cases hil : i.val = 2 * s + 3
  · have hi : i = ⟨2 * s + 3 - (0 : Fin (s + 1)).val, by omega⟩ := Fin.ext (by simpa using hil)
    have hnext : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 4)) := by
      apply Fin.ext
      change (i.val + 1) % (2 * s + 4) = 0
      rw [show i.val + 1 = 2 * s + 4 by omega, Nat.mod_self]
    rw [hnext, hi, coefficientShearResidueCycleComponent_second,
      coefficientShearResidueCycleComponent_exterior,
      coefficientShearResidueBranchComponent_initial]
    exact (coefficientShearResidueExterior_initial_second
      hπ hm data s hs hk hstart h3 h4 h6 hc).symm
  · let j : Fin s := ⟨2 * s + 2 - i.val, by omega⟩
    have hi : i = ⟨2 * s + 3 - j.succ.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hi' : (⟨i.val + 1, by omega⟩ : Fin (2 * s + 4)) =
        ⟨2 * s + 3 - j.castSucc.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hn (by omega), hi']
    conv_lhs => rw [hi]
    rw [coefficientShearResidueCycleComponent_second,
      coefficientShearResidueCycleComponent_second]
    exact (coefficientShearResidueBranchComponent_endpoints
      hπ hm data s hs hk hstart h3 h4 h6 hc j 1).symm

end FLT.Mazur.WeierstrassDividedDepth
