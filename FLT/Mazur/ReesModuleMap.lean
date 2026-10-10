/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesAlgebraMap
public import Mathlib.RingTheory.Filtration

/-!
# Semilinear maps of filtered Rees modules

Coefficientwise semilinear maps preserve polynomial convolution. Restricting
to compatible filtrations gives maps over the actual Rees algebra maps,
including the scalar changes needed for affine-open restriction.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.Rees

variable {R S : Type*} [CommRing R] [CommRing S]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  {f : R →+* S} (g : M →ₛₗ[f] N)

/-- The coefficientwise semilinear map on polynomial modules. -/
def polynomialMap : PolynomialModule R M →ₛₗ[f] PolynomialModule S N :=
  (PolynomialModule.coeffLinearEquiv S S).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap g).comp (PolynomialModule.coeffLinearEquiv R R).toLinearMap)

/-- The original semilinear map acts on each coefficient. -/
lemma polynomialMap_coeff (p : PolynomialModule R M) (n : ℕ) :
    (polynomialMap g p).coeff n = g (p.coeff n) := rfl

/-- Homogeneous inputs retain their degrees. -/
lemma polynomialMap_single (n : ℕ) (m : M) :
    polynomialMap g (PolynomialModule.single R n m) =
      PolynomialModule.single S n (g m) := by
  apply PolynomialModule.ext
  exact Finsupp.mapRange_single (hf := map_zero g)

/-- Coefficientwise semilinearity respects the full polynomial scalar action. -/
lemma polynomialMap_smul (r : R[X]) (p : PolynomialModule R M) :
    polynomialMap g (r • p) = r.map f • polynomialMap g p := by
  ext n
  simp only [polynomialMap_coeff, PolynomialModule.smul_apply, map_sum,
    map_smulₛₗ, Polynomial.coeff_map]

variable (I : Ideal R) (J : Ideal S) (hf : I.map f ≤ J)
  (F : I.Filtration M) (G : J.Filtration N)
  (hg : ∀ n, ∀ x ∈ F.N n, g x ∈ G.N n)

/-- Restriction of the coefficientwise map to the actual filtered Rees modules. -/
def moduleMap : F.submodule →ₛₗ[algebraMap I J f hf] G.submodule where
  toFun p := ⟨polynomialMap g p.val, fun n ↦ hg n (p.val.coeff n) (p.property n)⟩
  map_add' p q := Subtype.ext (map_add (polynomialMap g) p.val q.val)
  map_smul' r p := Subtype.ext (polynomialMap_smul g r.val p.val)

/-- The map on filtered modules still uses the original coefficients. -/
lemma moduleMap_coeff (p : F.submodule) (n : ℕ) :
    (moduleMap g I J hf F G hg p).val.coeff n = g (p.val.coeff n) := rfl

/-- Injectivity of a coefficient map implies injectivity on the filtered Rees modules. -/
lemma moduleMap_injective (hinj : Function.Injective g) :
    Function.Injective (moduleMap g I J hf F G hg) := by
  intro p q h
  apply Subtype.ext
  ext n
  exact hinj (congrArg (fun x : G.submodule ↦ x.val.coeff n) h)

end FLT.Mazur.Rees
