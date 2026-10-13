/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueInitialCoconeDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorInfinity
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent

/-!
# All full atlas maps from an arbitrary original residue pinching cocone

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
open WeierstrassModificationX
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4)
    (Nat.zero_lt_succ (2 * s + 3)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 4) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 4) (by omega) C.inl C.inr C.condition i

local notation "hk" => Nat.le_of_eq he
local notation "P" => residueInfinityTensorParameter d (show 0 < start + 0 from by omega)
  (nodalDepth_residue_uniformizer hm) a ha

/-- An actual pinching cocone supplies a map on the entire original infinity equation. -/
@[irreducible] def coefficientShearResidueInfinityCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 0) ⟶ C.pt.left :=
  P ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0

omit [IsDomain R] in
/-- The entire infinity map preserves the original residue-tangent coefficient structure. -/
theorem coefficientShearResidueInfinityCoconeDesc_structure :
    coefficientShearResidueInfinityCoconeDesc hm data s hs hstart h3 h4 hc C ≫ C.pt.hom =
      coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0) := by
  have hf : F 0 ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 4) 0 ≫ C.inl).w
  rw [coefficientShearResidueInfinityCoconeDesc]
  simp only [Category.assoc]
  rw [hf, ProjectiveLine.slopeNormalizationIso_base, residueInfinityTensorParameter_structure]
  rfl

/-- Every complete actual atlas chart receives a morphism from the original pinching cocone. -/
@[irreducible] def coefficientShearResidueAtlasCoconeMap (i : Fin 3 ⊕ Fin (s + 1)) :
    coefficientShearAtlasObject data Q r (s + 1) hs i ⟶ C.pt.left := by
  match i with
  | .inl k =>
    exact Fin.cases
      (coefficientShearResidueInfinityCoconeDesc hm data s hs hstart h3 h4 hc C)
      (Fin.cases
        (coefficientShearResidueDividedDesc hπ hm data s hs he h3 h4 h6next hc F)
        (fun _ => coefficientShearResidueInitialCoconeDesc
          hπ hm data s hs hk hstart h3 h4 h6 hc C)) k
  | .inr j =>
    by_cases hj : j.val = s
    · have H : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hj
      subst j
      exact coefficientShearResidueLastDesc hπ hm data s hs he h3 h4 h6next hc hstart F w
    · exact coefficientShearResidueInteriorDesc
        hπ hm data s hs h3 h4 hc ⟨j.val, by omega⟩ hstart F w
local notation "D" => coefficientShearResidueAtlasCoconeMap
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C

/-- The complete infinity chart is the actual original exterior parameter. -/
theorem coefficientShearResidueAtlasCoconeMap_infinity :
    D (.inl 0) = coefficientShearResidueInfinityCoconeDesc
      hm data s hs hstart h3 h4 hc C := by
  rw [coefficientShearResidueAtlasCoconeMap]
  rfl

/-- The entire divided equation uses the actual equality component. -/
theorem coefficientShearResidueAtlasCoconeMap_divided :
    D (.inl 1) = coefficientShearResidueDividedDesc
      hπ hm data s hs he h3 h4 h6next hc F := by
  rw [coefficientShearResidueAtlasCoconeMap]
  rfl

/-- The initial equation reuses the previously constructed full cocone descent. -/
theorem coefficientShearResidueAtlasCoconeMap_initial :
    D (.inl 2) = coefficientShearResidueInitialCoconeDesc
      hπ hm data s hs hk hstart h3 h4 h6 hc C := by
  rw [coefficientShearResidueAtlasCoconeMap]
  rfl

/-- Every interior retained equation uses both full conic branches and both whole lines. -/
theorem coefficientShearResidueAtlasCoconeMap_interior (j : Fin s) :
    D (.inr j.castSucc) = coefficientShearResidueInteriorDesc
      hπ hm data s hs h3 h4 hc j hstart F w := by
  rw [coefficientShearResidueAtlasCoconeMap]
  simp only [show ¬j.castSucc.val = s from by simp only [Fin.val_castSucc]; omega, ↓reduceDIte]
  rfl

/-- The last retained equation uses its original nonzero-constant conic. -/
theorem coefficientShearResidueAtlasCoconeMap_last :
    D (.inr ⟨s, Nat.lt_succ_self s⟩) = coefficientShearResidueLastDesc
      hπ hm data s hs he h3 h4 h6next hc hstart F w := by
  rw [coefficientShearResidueAtlasCoconeMap]
  simp only [↓reduceDIte]

end FLT.Mazur.WeierstrassDividedDepth
