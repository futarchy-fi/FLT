/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLocalizationSquare
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Algebra maps from affine morphisms over a coefficient spectrum

A proved scalar triangle recovers an algebra homomorphism, retaining the
entire affine morphism. Principal localizations preserve this triangle.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineScalarMap

universe u

variable (R : Type u) [CommRing R]

/-- The coefficient-spectrum morphism of an algebra. -/
def base (S : Type u) [CommRing S] [Algebra R S] : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

variable {R} {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The spectrum of an algebra map preserves its coefficients. -/
@[reassoc] theorem map_fac (f : S →ₐ[R] T) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ base R S = base R T := by
  rw [base, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext f.comp_algebraMap

/-- Principal open inclusions preserve the coefficient morphism. -/
@[reassoc] theorem inclusion_fac (r : S) :
    PrincipalLocalizationSquare.inclusion r ≫ base R S = base R (Localization.Away r) :=
  map_fac (Algebra.algHom R S (Localization.Away r))

/-- Recover an algebra map from a morphism with a proved coefficient triangle. -/
def ofHom (f : Spec (.of T) ⟶ Spec (.of S))
    (hf : f ≫ base R S = base R T) : S →ₐ[R] T := by
  refine { (Spec.preimage f).hom with commutes' := ?_ }
  intro r
  have h : Spec.map (CommRingCat.ofHom
      ((Spec.preimage f).hom.comp (algebraMap R S))) =
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage f) = _
    rw [Spec.map_comp, Spec.map_preimage]
    exact hf
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) r

/-- Recovering the algebra homomorphism retains the full scheme morphism. -/
theorem ofHom_spec (f : Spec (.of T) ⟶ Spec (.of S))
    (hf : f ≫ base R S = base R T) :
    Spec.map (CommRingCat.ofHom (ofHom f hf).toRingHom) = f :=
  Spec.map_preimage f

end FLT.Mazur.AffineScalarMap
