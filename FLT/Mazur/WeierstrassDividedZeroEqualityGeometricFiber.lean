/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityFieldPolygon

import all FLT.Mazur.WeierstrassDividedZeroEqualityPolygonIso

/-!
# Classification of every chosen equality-depth geometric fiber

Every field-valued point of the residue base gives the specified polygon on
any actual pullback square, without choosing an algebra structure in advance.
The result applies in particular to algebraically closed geometric fields.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "N" => zeroEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => zeroEqualityCycleNodes hπ data D s hs hk
variable (L : Type u) [Field L] (g : Spec (.of L) ⟶ Spec (.of (ResidueField R)))
  {Y : Scheme.{u}} (fst : Y ⟶ finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs)
  (snd : Y ⟶ Spec (.of L))
  (hY : IsPullback fst snd
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))))
      (finiteGlobalStructure hπ data (s + 1) hs)) g)

include D hstart hk hp hY in
/-- Any chosen field-valued pullback has the actual specified polygon pinching cocone. -/
theorem zeroEqualityGeometricFiber_exists_cocone :
    ∃ (a : PolygonPinching.components L (2 * s + 2) ⟶ Over.mk snd)
      (b : PolygonPinching.nodes L (2 * s + 2) ⟶ Over.mk snd),
      IsPushout (PolygonPinching.toComponents L (2 * s + 2) (by omega))
        (PolygonPinching.toNodes L (2 * s + 2)) a b :=
  PolygonFieldExtension.exists_cocone_of_isPullback K L (2 * s + 2) (by omega) N Q
    (zeroEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp) g fst snd hY

include D hstart hk hp hY in
/-- Every actual geometric fiber is isomorphic over its field to the specified polygon. -/
theorem zeroEqualityGeometricFiber_nonempty_iso :
    Nonempty (PolygonAtlas.polygon L (2 * s + 2) ≅ Over.mk snd) := by
  obtain ⟨a, b, h⟩ := zeroEqualityGeometricFiber_exists_cocone
    hπ data D s hs hstart hk hp L g fst snd hY
  exact ⟨PolygonPinching.polygonIso L (2 * s + 2) (by omega) a b h⟩

include D hstart hk hp hY in
/-- The same classification identifies the entire underlying geometric fiber scheme. -/
theorem zeroEqualityGeometricFiber_nonempty_schemeIso :
    Nonempty ((PolygonAtlas.polygon L (2 * s + 2)).left ≅ Y) := by
  obtain ⟨e⟩ := zeroEqualityGeometricFiber_nonempty_iso
    hπ data D s hs hstart hk hp L g fst snd hY
  exact ⟨(Over.forget _).mapIso e⟩

end FLT.Mazur.WeierstrassDividedDepth
