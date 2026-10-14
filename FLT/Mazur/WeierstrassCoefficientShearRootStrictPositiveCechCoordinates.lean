/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveTangentCoordinates
public import FLT.Mazur.WeierstrassCoefficientShearTangentRootCech

/-!
# The original tangent Cech transport in explicit strict polygon coordinates

Evaluate the original integral overlap at the two actual split roots. Its
whole-model transport becomes the intrinsic reflection between the two orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => coefficientShearRootStrictPositiveCoordinates
  hπ data D s hs hstart hk hp
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp
local notation "ρ" => coefficientShearRootStrictPositivePolygonReflectionIso
  hπ data D s hs hstart hk hp

local notation "t" => -algebraMap R K W.a₁
local notation "h0" => coefficientShearSplitRoot_zero D
local notation "ht" => coefficientShearSplitRoot_companion D
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "root" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "a" => pullback.fst q q
local notation "b" => pullback.snd q q
local notation "M" => coefficientShearTransport hπ data A root (s + 1) hs a b pullback.condition
local notation "L₀" => coefficientShearTangentRootCechFirst hπ data K 0 t h0 ht (s + 1) hs
local notation "Lt" => coefficientShearTangentRootCechSecond hπ data K 0 t h0 ht (s + 1) hs

/-- The original whole-model Cech transport is reflection in the explicit two orientations. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_cechTransport :
    (C 0).hom ≫ L₀ ≫ (M).hom = (ρ).hom ≫ (O t).hom ≫ Lt := by
  rw [coefficientShearTangentRootCech_transport, ← Category.assoc,
    coefficientShearRootStrictPositiveCoordinates_rootChange_reflection, Category.assoc]

/-- Reconstruction retains the original integral Cech comparison in these coordinates. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCoordinates_cechOriginal :
    (C 0).hom ≫ L₀ ≫ coefficientShearOverlapReconstruction hπ data A root (s + 1) hs a ≫
        (finiteGlobalTangentCechIso hπ data (s + 1) hs).hom =
      (ρ).hom ≫ (O t).hom ≫ Lt ≫
        coefficientShearOverlapReconstruction hπ data A root (s + 1) hs b := by
  rw [coefficientShearTangentRootCech_original, ← Category.assoc,
    coefficientShearRootStrictPositiveCoordinates_rootChange_reflection, Category.assoc]

/-- Every effectively compatible integral map obeys the full polygon comparison. -/
theorem coefficientShearRootStrictPositiveCoordinates_cechCompatible {Y : Scheme}
    (k : coefficientShearGlued hπ data A root (s + 1) hs ⟶ Y)
    (hcompat : pullback.snd a (coefficientShearGluedStructure hπ data A root (s + 1) hs) ≫ k =
      (M).hom ≫ pullback.snd b
        (coefficientShearGluedStructure hπ data A root (s + 1) hs) ≫ k) :
    (C 0).hom ≫ coefficientShearTangentRootSpecialization hπ data K 0 h0 (s + 1) hs ≫ k =
      (ρ).hom ≫ (O t).hom ≫
        coefficientShearTangentRootSpecialization hπ data K t ht (s + 1) hs ≫ k := by
  rw [coefficientShearTangentRootCech_compatible hπ data K 0 t h0 ht (s + 1) hs k hcompat,
    ← Category.assoc, coefficientShearRootStrictPositiveCoordinates_rootChange_reflection,
    Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
