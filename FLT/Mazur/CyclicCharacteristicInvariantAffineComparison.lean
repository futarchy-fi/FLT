/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantLocallyRinged
public import FLT.Mazur.CyclicCharacteristicInvariantSectionRings
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Affine comparison maps for invariant quotient opens

For each quotient open, construct the spectrum of its actual invariant section
ring and the canonical locally ringed comparison map. Its basic-open preimages
are the unit loci of invariant functions. These are comparison targets, not
proved affine charts: proving suitable comparisons are isomorphisms still
requires the normalized parameter geometry and invariant localization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))

/-- The explicit locally ringed quotient restricted to an actual orbit open. -/
def invariantOpenSpace : LocallyRingedSpace :=
  (invariantLocallyRingedSpace n).restrict W.isOpenEmbedding

/-- Global functions on the restricted quotient are precisely invariant sections on the open. -/
def invariantOpenSectionsIso :
    LocallyRingedSpace.Γ.obj (op (invariantOpenSpace n W)) ≅
      (invariantSheaf n).obj.obj (op W) :=
  (invariantSheaf n).obj.mapIso (eqToIso (by
    apply congrArg op
    exact Opens.isOpenEmbedding_obj_top (X := space n) W))

/-- An actual affine scheme constructed from the invariant regular-function ring. -/
def invariantAffineTarget : Scheme :=
  Spec ((invariantSheaf n).obj.obj (op W))

/-- The canonical comparison from the quotient open to its invariant affine target. -/
def invariantAffineComparison : invariantOpenSpace n W ⟶
    (invariantAffineTarget n W).toLocallyRingedSpace :=
  (invariantOpenSpace n W).toΓSpec ≫
    Spec.locallyRingedSpaceMap (invariantOpenSectionsIso n W).inv

/-- The comparison's prime ideal tests units of the corresponding actual invariant germ. -/
theorem invariantAffineComparison_notMem (r : (invariantSheaf n).obj.obj (op W))
    (x : invariantOpenSpace n W) :
    r ∉ ((invariantAffineComparison n W).base x).asIdeal ↔
      IsUnit ((invariantOpenSpace n W).presheaf.Γgerm x
        ((invariantOpenSectionsIso n W).inv r)) :=
  (invariantOpenSpace n W).notMem_prime_iff_unit_in_stalk
    ((invariantOpenSectionsIso n W).inv r) x

/-- Basic opens in the actual affine target pull back to invariant unit loci. -/
theorem invariantAffineComparison_preimage_basicOpen
    (r : (invariantSheaf n).obj.obj (op W)) :
    (invariantAffineComparison n W).base ⁻¹' (PrimeSpectrum.basicOpen r).carrier =
      ((invariantOpenSpace n W).toRingedSpace.basicOpen
        ((invariantOpenSectionsIso n W).inv r) : Set _) := by
  ext x
  exact (invariantAffineComparison_notMem n W r x).trans
    ((invariantOpenSpace n W).toRingedSpace.mem_top_basicOpen _ x).symm

end FLT.Mazur.CyclicCharacteristicOrbit
