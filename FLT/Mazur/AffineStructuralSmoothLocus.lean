/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusSpec

/-!
# Smoothness for the original affine coefficient map

The affine section algebra uses the actual structural pullback, including
the canonical identification of coefficients with sections on their spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineStructuralSmoothLocus

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  (U : X.affineOpens)

/-- The coefficient map on an actual affine open over an affine base. -/
def scalars : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The original affine chart is over precisely its structural coefficient map. -/
theorem fromSpec_toBase :
    U.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (scalars f U)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The actual affine coefficient map retains the image prime on the base. -/
theorem scalar_mem_primeIdealOf_iff (x : U.1) (r : R) :
    scalars f U r ∈ (U.2.primeIdealOf x).asIdeal ↔ r ∈ (f x.val).asIdeal := by
  have he := congrArg (fun g ↦ g (U.2.primeIdealOf x)) (fromSpec_toBase f U)
  rw [Scheme.Hom.comp_apply, U.2.fromSpec_primeIdealOf] at he
  rw [he]
  rfl

/-- The original affine prime tests membership in the actual relative smooth locus. -/
theorem mem_smoothLocus_iff [LocallyOfFinitePresentation f] (x : U.1) :
    let _ := (scalars f U).toAlgebra
    x.val ∈ f.smoothLocus ↔ Algebra.IsSmoothAt R (U.2.primeIdealOf x).asIdeal := by
  let _ := (scalars f U).toAlgebra
  have he := fromSpec_toBase f U
  let _ : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) :=
    he ▸ inferInstanceAs (LocallyOfFinitePresentation (U.2.fromSpec ≫ f))
  rw [← U.2.fromSpec_primeIdealOf x]
  change U.2.primeIdealOf x ∈ U.2.fromSpec ⁻¹ᵁ f.smoothLocus ↔ _
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  rw! [he]
  exact Spec.mem_smoothLocus_iff (U.2.primeIdealOf x)

/-- Specialization in an affine open is inclusion of the actual section prime ideals. -/
theorem primeIdealOf_le_of_specializes (x y : U.1) (hxy : x.val ⤳ y.val) :
    (U.2.primeIdealOf x).asIdeal ≤ (U.2.primeIdealOf y).asIdeal := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mpr
  have hxy' : x ⤳ y := U.1.isOpenEmbedding'.isInducing.specializes_iff.mp hxy
  exact hxy'.map U.2.isoSpec.hom.continuous

end FLT.Mazur.AffineStructuralSmoothLocus
