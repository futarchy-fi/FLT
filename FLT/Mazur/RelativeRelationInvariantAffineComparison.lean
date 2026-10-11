/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocallyRinged
public import FLT.Mazur.RelativeRelationInvariantSections
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Affine comparison maps for invariant quotient opens

For each quotient open, construct the spectrum of its actual invariant section
ring and the canonical locally ringed comparison map. Its basic-open preimages
are the unit loci of invariant functions. These are comparison targets, not
proved affine charts: proving suitable comparisons are isomorphisms still
requires the special Picard geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))

/-- The explicit locally ringed quotient restricted to an actual orbit open. -/
def invariantOpenSpace : LocallyRingedSpace.{u} :=
  (invariantLocallyRingedSpace e).restrict W.isOpenEmbedding

/-- Global functions on the restricted quotient are precisely invariant sections on the open. -/
def invariantOpenSectionsIso :
    LocallyRingedSpace.Γ.obj (op (invariantOpenSpace e W)) ≅
      (invariantSheaf e).obj.obj (op W) :=
  (invariantSheaf e).obj.mapIso (eqToIso (by
    apply congrArg op
    exact Opens.isOpenEmbedding_obj_top (X := space e) W))

/-- An actual affine scheme constructed from the invariant regular-function ring. -/
def invariantAffineTarget : Scheme.{u} :=
  Spec ((invariantSheaf e).obj.obj (op W))

/-- The canonical comparison from the quotient open to its invariant affine target. -/
def invariantAffineComparison : invariantOpenSpace e W ⟶
    (invariantAffineTarget e W).toLocallyRingedSpace :=
  (invariantOpenSpace e W).toΓSpec ≫
    Spec.locallyRingedSpaceMap (invariantOpenSectionsIso e W).inv

/-- The comparison's prime ideal tests units of the corresponding actual invariant germ. -/
theorem invariantAffineComparison_notMem (r : (invariantSheaf e).obj.obj (op W))
    (x : invariantOpenSpace e W) :
    r ∉ ((invariantAffineComparison e W).base x).asIdeal ↔
      IsUnit ((invariantOpenSpace e W).presheaf.Γgerm x
        ((invariantOpenSectionsIso e W).inv r)) :=
  (invariantOpenSpace e W).notMem_prime_iff_unit_in_stalk
    ((invariantOpenSectionsIso e W).inv r) x

/-- Basic opens in the actual affine target pull back to invariant unit loci. -/
theorem invariantAffineComparison_preimage_basicOpen
    (r : (invariantSheaf e).obj.obj (op W)) :
    (invariantAffineComparison e W).base ⁻¹' (PrimeSpectrum.basicOpen r).carrier =
      ((invariantOpenSpace e W).toRingedSpace.basicOpen
        ((invariantOpenSectionsIso e W).inv r) : Set _) := by
  ext x
  exact (invariantAffineComparison_notMem e W r x).trans
    ((invariantOpenSpace e W).toRingedSpace.mem_top_basicOpen _ x).symm

end FLT.Mazur.RelativeRelationOrbit
