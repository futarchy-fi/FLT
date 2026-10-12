/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearFiniteModification
public import FLT.Mazur.WeierstrassShearInfinityPreimage
public import FLT.Mazur.WeierstrassDividedFiniteYBoundary
public import FLT.Mazur.SchemeUnchangedOpenIsoSquare

/-!
# The actual affine contraction and translated infinity boundary

The finite modification comparison lies over the actual affine shear.
Consequently the whole original finite contraction is unchanged over the
translated infinity boundary D(y+r*x), with the full inverse image retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
  (j : ℕ) (hj : j ≤ n)
local notation "dat" => fun a => shearData (data a) r
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "a" => affineVariableChangeIso W U C rfl
local notation "m" => shearFiniteModificationIso hπ data r j hj

/-- The entire finite modification shear retains the original affine contraction. -/
@[reassoc] theorem shearFiniteModificationIso_toAffine :
    (m).hom ≫ finiteToAffine hπ data j hj = finiteToAffine hπ dat j hj ≫ (a).hom := by
  apply (cancel_mono (integralCurveChart W 2)).mp
  rw [Category.assoc, finiteToAffine_toCurve, Category.assoc,
    ← integralVariableChangeIso_affine, ← Category.assoc, finiteToAffine_toCurve]
  exact shearFiniteModificationIso_toCurve hπ data r j hj

/-- The full affine contraction square is cartesian, including all exceptional functions. -/
theorem shearFiniteModificationIso_affine_isPullback :
    IsPullback (m).hom (finiteToAffine hπ dat j hj)
      (finiteToAffine hπ data j hj) (a).hom :=
  IsPullback.of_horiz_isIso ⟨shearFiniteModificationIso_toAffine hπ data r j hj⟩

omit [IsDomain R] in
/-- The original infinity boundary has precisely the translated defining function. -/
theorem shearAffine_originalY_preimage :
    (a).hom ⁻¹ᵁ PrimeSpectrum.basicOpen (coord W 2 1) =
      PrimeSpectrum.basicOpen (coord U 2 1 + algebraMap R (Coordinate U 2) r * coord U 2 0) := by
  change Spec.map (CommRingCat.ofHom (affineVariableChangeMap W U C rfl).toRingHom) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (coord W 2 1) = _
  rw [SpecMap_preimage_basicOpen]
  congr 1
  change affineVariableChangeMap W U C rfl (coord W 2 1) = _
  simp only [affineVariableChangeMap_y, Units.val_one, map_one, one_pow, one_mul,
    map_zero, add_zero]

variable [IsBezout R]

/-- The entire finite sheared contraction is unchanged on the actual translated Y-boundary. -/
theorem finiteToAffine_shearOriginalY_isIso :
    IsIso (finiteToAffine hπ dat j hj ∣_
      PrimeSpectrum.basicOpen (coord U 2 1 + algebraMap R (Coordinate U 2) r * coord U 2 0)) := by
  rw [← shearAffine_originalY_preimage (W := W) r]
  exact SchemeUnchangedOpen.isIso_of_iso_square m a (finiteToAffine hπ data j hj)
    (finiteToAffine hπ dat j hj) (shearFiniteModificationIso_toAffine hπ data r j hj)
    (PrimeSpectrum.basicOpen (coord W 2 1)) (finiteToAffine_originalY_isIso hπ data j hj)

end FLT.Mazur.WeierstrassDividedDepth
