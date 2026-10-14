/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroExteriorMaps
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroRetainedDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictDividedDescent

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroExteriorMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroRetainedDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictDividedDescent

/-!
# The entire original strict start-zero atlas receives its cyclic cocone

This joins the full exterior equations to every retained and divided map,
including the length-zero terminal pair. Overlap compatibility remains to be proved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)
    (Nat.zero_lt_succ (2 * s + 2)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

/-- Every complete zero-start atlas equation receives the original strict cyclic cocone. -/
@[irreducible] def coefficientShearResidueStrictZeroAtlasCoconeMap
    (i : Fin 3 ⊕ Fin (s + 1)) :
    coefficientShearAtlasObject data Q r (s + 1) hs i ⟶ C.pt.left := by
  rcases i with k | j
  · exact Fin.cases
      (coefficientShearResidueStrictZeroInfinityCoconeDesc hm data s hs h3 h4 hc C)
      (Fin.cases
        (coefficientShearResidueStrictDividedDesc
          hπ hm data s hs hk h3 h4 h6 hc s (2 * s + 3) (by omega) F w)
        (fun _ => coefficientShearResidueStrictZeroInitialCoconeDesc
          hπ hm data s hs h3 h4 hc C)) k
  · exact Fin.cases
      (coefficientShearResidueStrictZeroFirstCoconeDesc hπ hm data s hs hk h3 h4 h6 hc C)
      (fun j => coefficientShearResidueStrictZeroRetainedDesc
        hπ hm data s hs hk h3 h4 h6 hc j.succ (Nat.succ_pos _) F w) j
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C

/-- The infinity entry is the entire original exterior parameter. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_infinity :
    D (.inl 0) = coefficientShearResidueStrictZeroInfinityCoconeDesc
      hm data s hs h3 h4 hc C := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
  rfl

/-- The divided entry uses both full actual terminal branches. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_divided :
    D (.inl 1) = coefficientShearResidueStrictDividedDesc
      hπ hm data s hs hk h3 h4 h6 hc s (2 * s + 3) (by omega) F w := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
  rfl

/-- The initial entry is the full punctured slope line of the original exterior. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_initial :
    D (.inl 2) = coefficientShearResidueStrictZeroInitialCoconeDesc
      hπ hm data s hs h3 h4 hc C := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
  rfl

/-- The first retained entry uses both whole conic branches and the exterior line. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_first :
    D (.inr 0) = coefficientShearResidueStrictZeroFirstCoconeDesc
      hπ hm data s hs hk h3 h4 h6 hc C := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
  rfl

/-- Each positive retained entry, including the last, keeps all four original branches. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_positive (j : Fin s) :
    D (.inr j.succ) = coefficientShearResidueStrictZeroRetainedDesc
      hπ hm data s hs hk h3 h4 h6 hc j.succ (Nat.succ_pos _) F w := by
  rw [coefficientShearResidueStrictZeroAtlasCoconeMap]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
