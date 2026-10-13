/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstCoconeDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInteriorDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent

/-!
# Every retained start-zero chart receives the original cyclic cocone

The first chart uses its full scale-one conic and exterior; the remaining
charts retain the positive-scale conic branches or the equality terminal.
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
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

/-- An arbitrary original cyclic cocone supplies a map on every entire retained atlas chart. -/
@[irreducible] def coefficientShearResidueZeroRetainedCoconeMap (j : Fin (s + 1)) :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inr j) ⟶ C.pt.left := by
  by_cases h0 : j.val = 0
  · have hj : j = ⟨0, Nat.zero_lt_succ s⟩ := Fin.ext h0
    subst j
    by_cases hs0 : s = 0
    · subst s
      exact coefficientShearResidueZeroLengthTwoCoconeDesc
        hπ hm data hs he h3 h4 h6next hc C
    · exact coefficientShearResidueZeroFirstCoconeDesc
        hπ hm data s hs (Nat.pos_of_ne_zero hs0) h3 h4 hc C
  · by_cases hlast : j.val = s
    · have hj : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hlast
      subst j
      exact coefficientShearResidueZeroLastDesc
        hπ hm data s hs he h3 h4 h6next hc (by simpa using Nat.pos_of_ne_zero h0) F w
    · exact coefficientShearResidueZeroInteriorDesc
        hπ hm data s hs h3 h4 hc ⟨j.val, by omega⟩ (Nat.pos_of_ne_zero h0) F w
local notation "D" => coefficientShearResidueZeroRetainedCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

/-- The first retained chart at positive chain length keeps its complete three-component descent. -/
theorem coefficientShearResidueZeroRetainedCoconeMap_first (hspos : 0 < s) :
    D ⟨0, Nat.zero_lt_succ s⟩ =
      coefficientShearResidueZeroFirstCoconeDesc hπ hm data s hs hspos h3 h4 hc C := by
  rw [coefficientShearResidueZeroRetainedCoconeMap]
  simp only [↓reduceDIte, dite_eq_right (Nat.ne_of_gt hspos)]

/-- Every positive interior chart keeps both original conic branches and both horizontal lines. -/
theorem coefficientShearResidueZeroRetainedCoconeMap_interior
    (j : Fin s) (hjpos : 0 < j.val) :
    D j.castSucc = coefficientShearResidueZeroInteriorDesc
      hπ hm data s hs h3 h4 hc j hjpos F w := by
  rw [coefficientShearResidueZeroRetainedCoconeMap]
  simp only [Fin.val_castSucc, dite_eq_right (Nat.ne_of_gt hjpos),
    dite_eq_right (Nat.ne_of_lt j.isLt)]

/-- The final positive retained chart keeps its original nonzero-constant equality conic. -/
theorem coefficientShearResidueZeroRetainedCoconeMap_last (hspos : 0 < s) :
    D ⟨s, Nat.lt_succ_self s⟩ = coefficientShearResidueZeroLastDesc
      hπ hm data s hs he h3 h4 h6next hc hspos F w := by
  rw [coefficientShearResidueZeroRetainedCoconeMap]
  simp only [dite_eq_right (Nat.ne_of_gt hspos), ↓reduceDIte]

/-- The same original cyclic cocone supplies the entire divided chart, including length two. -/
@[irreducible] def coefficientShearResidueZeroDividedCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 1) ⟶ C.pt.left :=
  coefficientShearResidueZeroDividedDesc hπ hm data s hs he h3 h4 h6next hc F

end FLT.Mazur.WeierstrassDividedDepth
