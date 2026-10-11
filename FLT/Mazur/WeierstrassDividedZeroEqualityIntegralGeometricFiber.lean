/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityGeometricFiber

/-!
# Geometric fibers of the actual integral equality-depth model

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
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

/-- The original integral fiber maps canonically to the actual residue model. -/
def equalityIntegralFiberToResidue : Y ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  pullback.lift (snd ≫ g) fst (by rw [Category.assoc]; exact hY.w.symm)
local notation "f" => equalityIntegralFiberToResidue hπ data s hs L g fst snd hY

/-- The residue lift preserves the chosen original integral projection. -/
@[reassoc] theorem equalityIntegralFiberToResidue_integral : f ≫ pullback.snd q t = fst :=
  pullback.lift_snd _ _ _

/-- The residue lift preserves the entire chosen coefficient morphism. -/
@[reassoc] theorem equalityIntegralFiberToResidue_residue : f ≫ p = snd ≫ g :=
  pullback.lift_fst _ _ _

/-- The original field fiber is also the exact field fiber of the residue model. -/
theorem equalityIntegralFiberToResidue_isPullback : IsPullback f snd p g := by
  have H : IsPullback (f ≫ pullback.snd q t) snd t (g ≫ q) := by
    rw [equalityIntegralFiberToResidue_integral]
    exact hY
  exact H.of_right (equalityIntegralFiberToResidue_residue hπ data s hs L g fst snd hY)
    (IsPullback.of_hasPullback q t).flip

include D hstart hk hp hY in
/-- Every chosen equality-depth geometric fiber of the integral model is the specified polygon. -/
theorem zeroEqualityIntegralGeometricFiber_nonempty_iso :
    Nonempty (PolygonAtlas.polygon L (2 * s + 2) ≅ Over.mk snd) :=
  zeroEqualityGeometricFiber_nonempty_iso hπ data D s hs hstart hk hp L g f snd
    (equalityIntegralFiberToResidue_isPullback hπ data s hs L g fst snd hY)

end FLT.Mazur.WeierstrassDividedDepth
