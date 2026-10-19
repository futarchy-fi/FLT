/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantAffineComparison

/-!
# Affine comparisons in original invariant-function coordinates

Identify the affine comparison target with the spectrum of the subring of
original source functions satisfying both full relation pullbacks. The map and
its prime-ideal test retain this identification, without a scheme structure
assumption on the orbit space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))
local notation "I" => originalInvariantSections n (Subtype.val (pullOpen n W))
  (pullOpen_preimage_eq n W)

/-- Spectrum of the actual compatible-function subring on the original source open. -/
def originalAffineTarget : Scheme := Spec (.of I)

/-- The affine target of the invariant sheaf is canonically the original invariant spectrum. -/
def originalAffineTargetIso : invariantAffineTarget n W ≅ originalAffineTarget n W :=
  (Scheme.Spec.mapIso (invariantSectionRingEquiv n W).toCommRingCatIso.op).symm

/-- The canonical orbit-open comparison expressed in original regular-function coordinates. -/
def originalAffineComparison : invariantOpenSpace n W ⟶
    (originalAffineTarget n W).toLocallyRingedSpace :=
  invariantAffineComparison n W ≫ (originalAffineTargetIso n W).hom.toLRSHom

/-- Original invariant coefficients are tested on the corresponding actual local germ. -/
theorem originalAffineComparison_notMem (r : I) (x : invariantOpenSpace n W) :
    r ∉ ((originalAffineComparison n W).base x).asIdeal ↔
      IsUnit ((invariantOpenSpace n W).presheaf.Γgerm x
        ((invariantOpenSectionsIso n W).inv ((invariantSectionRingEquiv n W).symm r))) :=
  invariantAffineComparison_notMem n W ((invariantSectionRingEquiv n W).symm r) x

/-- Original invariant basic opens pull back to the unit locus of the invariant section. -/
theorem originalAffineComparison_preimage_basicOpen (r : I) :
    (originalAffineComparison n W).base ⁻¹' (PrimeSpectrum.basicOpen r).carrier =
      ((invariantOpenSpace n W).toRingedSpace.basicOpen
        ((invariantOpenSectionsIso n W).inv ((invariantSectionRingEquiv n W).symm r)) :
          Set _) := by
  ext x
  exact (originalAffineComparison_notMem n W r x).trans
    ((invariantOpenSpace n W).toRingedSpace.mem_top_basicOpen _ x).symm

end FLT.Mazur.CyclicCharacteristicOrbit
