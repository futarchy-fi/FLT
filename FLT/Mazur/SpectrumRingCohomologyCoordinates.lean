/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRingCohomologyFinite
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Ring coordinates on spectrum cohomology

The spectrum global-section isomorphism transports actual cohomology,
its freeness, and its rank to the original coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.SpectrumRingCohomologyCoordinates

open FCurve Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) (M : X.Modules)

local instance spectrumCoefficientsInvPair :
    RingHomInvPair (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv

local instance spectrumCoefficientsInvPairReverse :
    RingHomInvPair (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toRingHom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv

/-- Changing from original coefficients to spectrum sections is semilinear transport. -/
def cohomologyEquiv (q : ℕ) :
    LinearEquiv
      (σ' := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toRingHom)
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom
      (ModuleRingH (baseCohomologyScalars f) M q) (ModuleRingH f.appTop.hom M q) where
  __ := AddEquiv.refl _
  map_smul' _ _ := rfl

/-- The actual cohomology has unchanged rank in the two coefficient coordinates. -/
theorem cohomology_finrank (q : ℕ) :
    Module.finrank Γ(Spec (.of R), ⊤) (ModuleRingH f.appTop.hom M q) =
      Module.finrank R (ModuleRingH (baseCohomologyScalars f) M q) := by
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have hr := rank_eq_of_equiv_equiv e.symm (cohomologyEquiv f M q).toAddEquiv
    e.symm.bijective (fun _ _ ↦ rfl)
  exact (congrArg Cardinal.toNat hr).symm

/-- Freeness of original cohomology transports to the spectrum global-section ring. -/
theorem cohomology_free (q : ℕ)
    [Module.Free R (ModuleRingH (baseCohomologyScalars f) M q)] :
    Module.Free Γ(Spec (.of R), ⊤) (ModuleRingH f.appTop.hom M q) :=
  Module.Free.of_equiv (cohomologyEquiv f M q)

end FLT.Mazur.SpectrumRingCohomologyCoordinates
