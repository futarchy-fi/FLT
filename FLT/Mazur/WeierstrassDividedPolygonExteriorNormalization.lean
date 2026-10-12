/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSplitNormalizationComparison
public import FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonIso

/-!
# The exterior in the actual polygon normalization is the constructed proper lift

Identify component zero of the proved split polygon comparison with the
proper-extension normalization. Both endpoints remain the original indexed nodes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "u₀" => Units.mk0 (residue R W.a₁)
  (IsUnit.ne_zero (WeierstrassModificationX.residue_tangent_isUnit D))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => finiteGlobalStructure hπ data (s + 1) hs
local notation "e" => positiveEqualityCyclePolygonIso hπ data D s hs hstart hk hp
local notation "N" => PolygonPinching.componentι K (2 * s + 4) 0 ≫
  PolygonAtlas.normalization K (2 * s + 4) ≫ Iso.hom e

/-- Component zero of the complete split normalization is the original ordered exterior. -/
theorem positiveEqualityPolygon_exterior :
    (N).left = initialOrientedToGlobal hπ data D (s + 1) hs hstart (by omega) (by omega) := by
  rw [positiveEqualityCyclePolygonIso_component, positiveEqualityCycleComponent_exterior]
  rfl

/-- The whole polygon exterior has the constructed complete original cubic projection. -/
@[reassoc] theorem positiveEqualityPolygon_exterior_contraction :
    (N).left ≫ pullback.snd q g ≫ finiteGlobalContraction hπ data (s + 1) hs =
      (slopeNormalizationIso u₀).inv ≫ initialSplitCompleteNormalization data D hstart := by
  rw [positiveEqualityPolygon_exterior, initialOrientedToGlobal_eq, Category.assoc,
    initialProjectiveToGlobal_contraction]

/-- The polygon's complete exterior is the unique constructed proper lift in ordered coordinates. -/
theorem positiveEqualityPolygon_exterior_lift :
    (N).left ≫ pullback.snd q g = (slopeNormalizationIso u₀).inv ≫
      projectiveFiniteLift hπ data (s + 1) hs
        (initialIncidenceNormalization data D hstart (by omega)).toRingHom
        (initialIncidenceNormalization_x_regular data D hstart (by omega))
        (initialSplitCompleteNormalization data D hstart)
        (initialSplitCompleteNormalization_left data D hstart (by omega)) := by
  rw [positiveEqualityPolygon_exterior, initialOrientedToGlobal_eq, Category.assoc,
    initialProjectiveToGlobal_eq_lift]

/-- The normalized zero marking remains the first indexed original node section. -/
@[reassoc] theorem positiveEqualityPolygon_exterior_zero :
    zero K ≫ (N).left =
      (equalityNodeOverSection hπ data D s hs hk (.inl ⟨0, hstart⟩)).left := by
  rw [positiveEqualityPolygon_exterior, initialOrientedToGlobal_zero]
  rfl

/-- The normalized infinity marking remains the second indexed original node section. -/
@[reassoc] theorem positiveEqualityPolygon_exterior_infinity :
    infinity K ≫ (N).left =
      (equalityNodeOverSection hπ data D s hs hk (.inl ⟨1, hstart⟩)).left := by
  rw [positiveEqualityPolygon_exterior, initialOrientedToGlobal_infinity]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
