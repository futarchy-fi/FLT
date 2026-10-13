/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps

/-!
# The entire original start-zero atlas receives a cyclic cocone

This joins the full initial and infinity equations to the retained and divided maps.
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
  (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

/-- Every full original atlas chart receives a map from the original cyclic cocone. -/
@[irreducible] def coefficientShearResidueZeroAtlasCoconeMap (i : Fin 3 ⊕ Fin (s + 1)) :
    coefficientShearAtlasObject data Q r (s + 1) hs i ⟶ C.pt.left := by
  rcases i with k | j
  · exact Fin.cases
      (coefficientShearResidueZeroInfinityCoconeDesc hm data s hs h3 h4 hc C)
      (Fin.cases
        (coefficientShearResidueZeroDividedCoconeDesc
          hπ hm data s hs he h3 h4 h6next hc C)
        (fun _ => coefficientShearResidueZeroInitialCoconeDesc
          hπ hm data s hs h3 h4 hc C)) k
  · exact coefficientShearResidueZeroRetainedCoconeMap
      hπ hm data s hs he h3 h4 h6next hc C j
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

/-- The infinity entry is the entire original infinity tensor equation. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_infinity :
    D (.inl 0) = coefficientShearResidueZeroInfinityCoconeDesc
      hm data s hs h3 h4 hc C := by
  rw [coefficientShearResidueZeroAtlasCoconeMap]
  rfl

/-- The divided entry keeps the entire original nonzero-constant equality parameter. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_divided :
    D (.inl 1) = coefficientShearResidueZeroDividedCoconeDesc
      hπ hm data s hs he h3 h4 h6next hc C := by
  rw [coefficientShearResidueZeroAtlasCoconeMap]
  rfl

/-- The initial entry is the whole scale-one slope localization. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_initial :
    D (.inl 2) = coefficientShearResidueZeroInitialCoconeDesc
      hπ hm data s hs h3 h4 hc C := by
  rw [coefficientShearResidueZeroAtlasCoconeMap]
  rfl

/-- Every retained entry keeps the previously constructed full equation map. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_retained (j : Fin (s + 1)) :
    D (.inr j) = coefficientShearResidueZeroRetainedCoconeMap
      hπ hm data s hs he h3 h4 h6next hc C j := by
  rw [coefficientShearResidueZeroAtlasCoconeMap]

end FLT.Mazur.WeierstrassDividedDepth
