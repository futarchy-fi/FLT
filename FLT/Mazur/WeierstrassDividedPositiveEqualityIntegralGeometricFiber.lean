/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityGeometricFiber
public import FLT.Mazur.WeierstrassDividedZeroEqualityIntegralGeometricFiber

/-!
# Geometric fibers of the positive-start integral equality-depth model

Pullback pasting identifies a chosen field fiber of the original integral
model with the corresponding fiber of its residue model. The proved polygon
classification therefore applies directly to the integral model's fibers.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "t" => finiteGlobalStructure hπ data (s + 1) hs
local notation "p" => pullback.fst q t
variable (L : Type u) [Field L] (g : Spec (.of L) ⟶ Spec (.of (ResidueField R)))
  {Y : Scheme.{u}} (fst : Y ⟶ finiteGlobalModel hπ data (s + 1) hs)
  (snd : Y ⟶ Spec (.of L))
  (hY : IsPullback fst snd (finiteGlobalStructure hπ data (s + 1) hs)
    (g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))))

local notation "f" => equalityIntegralFiberToResidue hπ data s hs L g fst snd hY

include D hstart hk hp hY in
/-- Every chosen equality-depth geometric fiber of the integral model is the specified polygon. -/
theorem positiveEqualityIntegralGeometricFiber_nonempty_iso :
    Nonempty (PolygonAtlas.polygon L (2 * s + 4) ≅ Over.mk snd) :=
  positiveEqualityGeometricFiber_nonempty_iso hπ data D s hs hstart hk hp L g f snd
    (equalityIntegralFiberToResidue_isPullback hπ data s hs L g fst snd hY)

end FLT.Mazur.WeierstrassDividedDepth
