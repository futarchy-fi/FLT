/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictInitialDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveRetainedDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictDividedDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorInfinity

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictDividedDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictInitialDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveRetainedDescent

/-!
# All full positive-start atlas maps of a strict residue pinching cocone

This constructs the chart family. Compatibility on full overlaps remains a separate obligation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)
    (Nat.zero_lt_succ (2 * s + 4)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 5) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 5) (by omega) C.inl C.inr C.condition i

local notation "P" => residueInfinityTensorParameter d (show 0 < start + 0 from by omega)
  (nodalDepth_residue_uniformizer hm) a ha

/-- An actual pinching cocone supplies a map on the entire original infinity equation. -/
@[irreducible] def coefficientShearResidueStrictInfinityCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 0) ⟶ C.pt.left :=
  P ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0

omit [IsDomain R] in
/-- The entire infinity map preserves the original residue-tangent coefficient structure. -/
theorem coefficientShearResidueStrictInfinityCoconeDesc_structure :
    coefficientShearResidueStrictInfinityCoconeDesc hm data s hs hstart h3 h4 hc C ≫ C.pt.hom =
      coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0) := by
  have hf : F 0 ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 5) 0 ≫ C.inl).w
  rw [coefficientShearResidueStrictInfinityCoconeDesc]
  simp only [Category.assoc]
  rw [hf, ProjectiveLine.slopeNormalizationIso_base, residueInfinityTensorParameter_structure]
  rfl

/-- Every complete positive-start atlas equation receives the original strict cyclic cocone. -/
@[irreducible] def coefficientShearResidueStrictPositiveAtlasCoconeMap
    (i : Fin 3 ⊕ Fin (s + 1)) :
    coefficientShearAtlasObject data Q r (s + 1) hs i ⟶ C.pt.left := by
  rcases i with k | j
  · exact Fin.cases
      (coefficientShearResidueStrictInfinityCoconeDesc hm data s hs hstart h3 h4 hc C)
      (Fin.cases
        (coefficientShearResidueStrictDividedDesc
          hπ hm data s hs hk h3 h4 h6 hc (s + 1) (2 * s + 5) (by omega) F w)
        (fun _ => coefficientShearResidueStrictInitialDesc
          hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc F w)) k
  · exact coefficientShearResidueStrictPositiveRetainedDesc
      hπ hm data s hs hk h3 h4 h6 hc j hstart F w
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C

/-- The infinity entry is the entire original exterior parameter. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_infinity :
    D (.inl 0) = coefficientShearResidueStrictInfinityCoconeDesc
      hm data s hs hstart h3 h4 hc C := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap]
  rfl

/-- The divided entry uses both full actual terminal branches. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_divided :
    D (.inl 1) = coefficientShearResidueStrictDividedDesc
      hπ hm data s hs hk h3 h4 h6 hc (s + 1) (2 * s + 5) (by omega) F w := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap]
  rfl

/-- The initial entry retains both full original initial branches and the incidence line. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_initial :
    D (.inl 2) = coefficientShearResidueStrictInitialDesc
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc F w := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap]
  rfl

/-- Every retained entry, including the last, keeps all four full original branches. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_retained (j : Fin (s + 1)) :
    D (.inr j) = coefficientShearResidueStrictPositiveRetainedDesc
      hπ hm data s hs hk h3 h4 h6 hc j hstart F w := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap]

end FLT.Mazur.WeierstrassDividedDepth
