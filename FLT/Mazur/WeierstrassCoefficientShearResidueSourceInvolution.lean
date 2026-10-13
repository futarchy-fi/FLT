/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResiduePinchingReflection
public import FLT.Mazur.CyclicPinchingSemilinearInvolution
import all FLT.Mazur.WeierstrassCoefficientShearResidueReflectionParameters

/-!
# Involutivity of the original residue pinching reflection

The original terminal constant comes from R, so conjugation fixes its unit.
This proves involutivity on each entire source of the original pinching span.
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
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next
local notation "c" => coefficientShearResidueReflectionScale hm data s hs he h6next

omit [IsDomain R] [IsBezout R] in
/-- The original residue coefficient automorphism squares to the identity. -/
theorem tangentResidueConjugation_comp_self :
    (f).toRingHom.comp (f).toRingHom = RingHom.id Q :=
  RingHom.ext (nodeTangentConjugationHom_involutive V)

omit [IsDomain R] [IsBezout R] in
/-- The actual terminal unit is fixed because its value is the original R constant. -/
theorem coefficientShearResidueTerminalUnit_conjugation :
    Units.map (f).toRingHom (cunit).unit = (cunit).unit := by
  apply Units.ext
  change f ((cunit).unit : Q) = ((cunit).unit : Q)
  rw [IsUnit.unit_spec]
  exact (f).commutes _

omit [IsDomain R] [IsBezout R] in
/-- Every scale, including the inverse original terminal constant, is coefficient-fixed. -/
theorem coefficientShearResidueReflectionScale_conjugation (i : Fin (2 * s + 4)) :
    Units.map (f).toRingHom (c i) = c i := by
  unfold coefficientShearResidueReflectionScale
  split_ifs
  · rw [map_inv, coefficientShearResidueTerminalUnit_conjugation hm data s hs he h6next]
  · exact map_one _

omit [IsDomain R] [IsBezout R] in
/-- The terminal is a fixed component, so reflection preserves the original scale function. -/
theorem coefficientShearResidueReflectionScale_reflect (i : Fin (2 * s + 4)) :
    c (PolygonPinching.reflectIndex i) = c i := by
  have hi : (PolygonPinching.reflectIndex i).val = s + 2 ↔ i.val = s + 2 := by
    constructor
    · intro h
      have hx : PolygonPinching.reflectIndex i = ⟨s + 2, by omega⟩ := Fin.ext h
      have := congrArg PolygonPinching.reflectIndex hx
      rw [PolygonPinching.reflectIndex_reflectIndex,
        PolygonPinching.reflectIndex_terminal] at this
      exact congrArg Fin.val this
    · intro h
      have hx : i = ⟨s + 2, by omega⟩ := Fin.ext h
      rw [hx, PolygonPinching.reflectIndex_terminal]
  simp only [coefficientShearResidueReflectionScale, hi]

omit [IsDomain R] [IsBezout R] in
/-- The exact full normalization reflection is an involution. -/
@[reassoc] theorem coefficientShearResidueSourceReflection_involutive :
    coefficientShearResidueSourceReflection hm data s hs he h6next ≫
      coefficientShearResidueSourceReflection hm data s hs he h6next = 𝟙 _ :=
  PolygonPinching.semilinearScaledComponents_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W)) c
    (coefficientShearResidueReflectionScale_conjugation hm data s hs he h6next)
    (coefficientShearResidueReflectionScale_reflect hm data s hs he h6next)

omit [IsDomain R] [IsBezout R] in
/-- The exact node reflection, with its coefficient conjugation, is an involution. -/
@[reassoc] theorem coefficientShearResidueNodesReflection_involutive :
    PolygonPinching.semilinearReflectionNodes (n := 2 * s + 4) (f).toRingHom ≫
      PolygonPinching.semilinearReflectionNodes (f).toRingHom = 𝟙 _ :=
  PolygonPinching.semilinearReflectionNodes_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

omit [IsDomain R] [IsBezout R] in
/-- The original branch exchange restores both full branch summands after two steps. -/
@[reassoc] theorem coefficientShearResidueBranchesReflection_involutive :
    PolygonPinching.semilinearReflectionBranches (n := 2 * s + 4) (f).toRingHom ≫
      PolygonPinching.semilinearReflectionBranches (f).toRingHom = 𝟙 _ :=
  PolygonPinching.semilinearReflectionBranches_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

end FLT.Mazur.WeierstrassDividedDepth
