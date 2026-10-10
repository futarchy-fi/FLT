/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbientCartesian
public import FLT.Mazur.HilbertPolynomialParameterIdeal
public import FLT.Mazur.HilbertPolynomialUniversalDegree

/-!
# Cartesian closed families of arbitrary Hilbert parameters

The coordinate ideal of every parameter gives its actual closed family.
The constructed comparison is cartesian over both ambient spaces and bases.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d =
  Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The actual closed family maps to the universal family over its ambient parameter. -/
def polynomialParameterClosedMap : (baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subscheme ⟶
    polynomialUniversalClosedFamily R I d :=
  IsClosedImmersion.lift (polynomialUniversalClosedImmersion R I d)
    ((baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subschemeι ≫
      polynomialAmbientMap R I d S f hf) (by
      rw [← map_bot ((baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subschemeι ≫
        polynomialAmbientMap R I d S f hf), le_map_iff_comap_le]
      change (polynomialUniversalIdeal R I d).comap _ ≤ ⊥
      rw [comap_comp, ← polynomialParameterIdeal_sheaf,
        ClosedIdealCover.comap_subschemeι_eq_bot])

/-- The family map preserves its original closed immersion in the polynomial ambient space. -/
@[reassoc]
theorem polynomialParameterClosedMap_immersion :
    polynomialParameterClosedMap R I d S f hf ≫ polynomialUniversalClosedImmersion R I d =
      (baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subschemeι ≫
        polynomialAmbientMap R I d S f hf := IsClosedImmersion.lift_fac _ _ _

/-- The closed-family comparison is uniquely determined by its ambient compatibility. -/
theorem polynomialParameterClosedMap_unique
    (g : (baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subscheme ⟶
      polynomialUniversalClosedFamily R I d)
    (hg : g ≫ polynomialUniversalClosedImmersion R I d =
      (baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subschemeι ≫
        polynomialAmbientMap R I d S f hf) :
    g = polynomialParameterClosedMap R I d S f hf := by
  apply (cancel_mono (polynomialUniversalClosedImmersion R I d)).mp
  rw [polynomialParameterClosedMap_immersion]
  exact hg

/-- The original closed family is the actual ambient pullback of the universal closed family. -/
theorem polynomialParameterClosedMap_ambient_isPullback :
    IsPullback (baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subschemeι
      (polynomialParameterClosedMap R I d S f hf) (polynomialAmbientMap R I d S f hf)
      (polynomialUniversalClosedImmersion R I d) := by
  apply isPullback_of_isClosedImmersion _ _ _ _
    (polynomialParameterClosedMap_immersion R I d S f hf).symm
  rw [ker_subschemeι]
  exact (polynomialParameterIdeal_sheaf R I d S f hf).symm

/-- The original closed family is the actual base change along its classifying parameter. -/
theorem polynomialParameterClosedMap_isPullback :
    IsPullback (polynomialParameterClosedMap R I d S f hf)
      ((baseIdeal (.of (MvPolynomial I S))
      (polynomialParameterIdeal R I d S f hf)).subschemeι ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
      (polynomialUniversalProjection R I d) f :=
  (polynomialParameterClosedMap_ambient_isPullback R I d S f hf).flip.paste_vert
    (polynomialAmbientMap_isPullback R I d S _ hf)

end FLT.Mazur.HilbertChart
