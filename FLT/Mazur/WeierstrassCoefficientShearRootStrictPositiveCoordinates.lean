/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveReflection
public import FLT.Mazur.WeierstrassCoefficientShearRootChange

/-!
# Explicit orientations of the complete strict split polygon

The first coordinates retain the independently assembled original components.
The opposite coordinates reverse every projective parameter and cyclic index
before changing the coefficient root. All original nodes are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "I" => (Over.forget _).mapIso
  (coefficientShearRootStrictPositivePolygonIso hπ data D s hs hstart hk hp)
local notation "F" => (Over.forget _).mapIso
  (coefficientShearRootStrictPositiveReflectionIso hπ data D s hs hstart hk hp)
local notation "Z" => coefficientShearRootStrictPositiveCycleComponent
  hπ data D s hs hstart hk hp
local notation "J" => coefficientShearRootStrictPositiveNodes hπ data D s hs hstart hk hp
local notation "N" => coefficientShearRootStrictPositiveNormalization hπ data D s hs hstart hk hp
local notation "P" => PolygonAtlas.polygon K (2 * s + 5)
local notation "PN" => (PolygonAtlas.normalization K (2 * s + 5)).left
local notation "PJ" => (PolygonAtlas.nodes K (2 * s + 5)).left

/-- Intrinsic reflection expressed on the specified full polygon. -/
def coefficientShearRootStrictPositivePolygonReflectionIso : (P).left ≅ (P).left :=
  I ≪≫ F ≪≫ (I).symm
local notation "ρ" => coefficientShearRootStrictPositivePolygonReflectionIso
  hπ data D s hs hstart hk hp

/-- Full first-orientation coordinates in any chosen coefficient presentation. -/
def coefficientShearRootStrictPositiveCoordinates (r : K) :
    (P).left ≅ coefficientShearGlued hπ data K r (s + 1) hs :=
  I ≪≫ coefficientShearRootChange hπ data K 0 r (s + 1) hs
local notation "Cr" => coefficientShearRootStrictPositiveCoordinates
  hπ data D s hs hstart hk hp

/-- Opposite coordinates reverse the complete original polygon before changing the root. -/
def coefficientShearRootStrictPositiveOppositeCoordinates (r : K) :
    (P).left ≅ coefficientShearGlued hπ data K r (s + 1) hs :=
  I ≪≫ F ≪≫ coefficientShearRootChange hπ data K 0 r (s + 1) hs
local notation "Or" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp

/-- The first coordinates retain the independent full normalization in its original order. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_normalization (r : K) :
    PN ≫ (Cr r).hom = (N).left ≫
      (coefficientShearRootChange hπ data K 0 r (s + 1) hs).hom := by
  have H := congrArg Over.Hom.left
    (coefficientShearRootStrictPositivePolygonIso_normalization hπ data D s hs hstart hk hp)
  simp only [Over.comp_left] at H
  change PN ≫ ((I).hom ≫ _) = _
  simp only [Functor.mapIso_hom, Over.forget_map]
  rw [← Category.assoc, H]

/-- Every full projective parameter has its original position in the first coordinates. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_component
    (r : K) (i : Fin (2 * s + 5)) :
    (PolygonPinching.componentι K (2 * s + 5) i).left ≫ PN ≫ (Cr r).hom =
      (Z i).left ≫ (coefficientShearRootChange hπ data K 0 r (s + 1) hs).hom := by
  rw [coefficientShearRootStrictPositiveCoordinates_normalization, ← Category.assoc]
  exact congrArg (fun f => f.left ≫
    (coefficientShearRootChange hπ data K 0 r (s + 1) hs).hom)
    (coefficientShearRootStrictPositiveNormalization_ι hπ data D s hs hstart hk hp i)

/-- Opposite coordinates reverse the full projective parameter at the reflected index. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_component
    (r : K) (i : Fin (2 * s + 5)) :
    (PolygonPinching.componentι K (2 * s + 5) i).left ≫ PN ≫ (Or r).hom =
      ProjectiveLine.endpointReversal K ≫ (Z (PolygonPinching.reflectIndex i)).left ≫
        (coefficientShearRootChange hπ data K 0 r (s + 1) hs).hom := by
  have H := congrArg Over.Hom.left
    (coefficientShearRootStrictPositivePolygonIso_normalization hπ data D s hs hstart hk hp)
  have HZ := congrArg Over.Hom.left
    (coefficientShearRootStrictPositiveNormalization_ι hπ data D s hs hstart hk hp i)
  have HF := congrArg Over.Hom.left
    (coefficientShearRootStrictPositiveReflection_component hπ data D s hs hstart hk hp i)
  simp only [Over.comp_left] at H HZ HF
  change _ ≫ PN ≫ ((I).hom ≫ (F).hom ≫ _) = _
  simp only [Functor.mapIso_hom, Over.forget_map,
    coefficientShearRootStrictPositiveReflectionIso]
  rw [← Category.assoc PN, H, ← Category.assoc, HZ,
    ← Category.assoc, HF, Category.assoc]
  rfl

/-- The opposite node coproduct is the full reflected original node coproduct. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_nodes (r : K) :
    PJ ≫ (Or r).hom = (PolygonPinching.nodesReflection K).left ≫ (J).left ≫
      (coefficientShearRootChange hπ data K 0 r (s + 1) hs).hom := by
  have H := congrArg Over.Hom.left
    (coefficientShearRootStrictPositivePolygonIso_nodes hπ data D s hs hstart hk hp)
  have HF := congrArg Over.Hom.left
    (coefficientShearRootStrictPositiveReflection_nodes hπ data D s hs hstart hk hp)
  simp only [Over.comp_left] at H HF
  change PJ ≫ ((I).hom ≫ (F).hom ≫ _) = _
  simp only [Functor.mapIso_hom, Over.forget_map,
    coefficientShearRootStrictPositiveReflectionIso]
  rw [← Category.assoc, H, ← Category.assoc, HF, Category.assoc]

/-- The original intrinsic reflection compares the two complete coordinate orientations. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_reflection (r : K) :
    (ρ).hom ≫ (Cr r).hom = (Or r).hom := by
  simp only [coefficientShearRootStrictPositivePolygonReflectionIso,
    coefficientShearRootStrictPositiveCoordinates,
    coefficientShearRootStrictPositiveOppositeCoordinates,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- Reflection is involutive on the actual full polygon, including every node. -/
@[reassoc] theorem coefficientShearRootStrictPositivePolygonReflection_involutive :
    (ρ).hom ≫ (ρ).hom = 𝟙 _ := by
  have HF := congrArg Over.Hom.left
    (coefficientShearRootStrictPositiveReflection_involutive hπ data D s hs hstart hk hp)
  simp only [Over.comp_left, Over.id_left] at HF
  have HF' : (F).hom ≫ (F).hom = 𝟙 _ := by
    simpa only [Functor.mapIso_hom, Over.forget_map, Over.forget_obj,
      coefficientShearRootStrictPositiveReflectionIso] using HF
  change ((I).hom ≫ (F).hom ≫ (I).inv) ≫ ((I).hom ≫ (F).hom ≫ (I).inv) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (F).hom, HF', Category.id_comp, Iso.hom_inv_id]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
