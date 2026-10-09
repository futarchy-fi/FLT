/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbientCartesian
public import FLT.Mazur.HilbertPolynomialUniversalFamilyPullback
public import FLT.Mazur.HilbertPolynomialUniversalDegree

/-!
# Recovering the actual closed family by base change

Universal ideal recovery induces a unique map of the original closed family
to the global universal family. Both the ambient square and the parameter
square are cartesian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- The actual closed family maps to the universal family over its ambient parameter. -/
def polynomialClosedFamilyMap : (baseIdeal (.of (MvPolynomial I S)) J).subscheme ⟶
    polynomialUniversalClosedFamily R I d :=
  IsClosedImmersion.lift (polynomialUniversalClosedImmersion R I d)
    ((baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
      polynomialFamilyAmbientMap R I d S J hd) (by
      rw [← map_bot ((baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
        polynomialFamilyAmbientMap R I d S J hd), le_map_iff_comap_le]
      change (polynomialUniversalIdeal R I d).comap _ ≤ ⊥
      rw [comap_comp, polynomialUniversalIdeal_familyPullback,
        ClosedIdealCover.comap_subschemeι_eq_bot])

/-- The family map preserves its original closed immersion in the polynomial ambient space. -/
@[reassoc]
theorem polynomialClosedFamilyMap_immersion :
    polynomialClosedFamilyMap R I d S J hd ≫ polynomialUniversalClosedImmersion R I d =
      (baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
        polynomialFamilyAmbientMap R I d S J hd := IsClosedImmersion.lift_fac _ _ _

/-- The closed-family comparison is uniquely determined by its ambient compatibility. -/
theorem polynomialClosedFamilyMap_unique
    (g : (baseIdeal (.of (MvPolynomial I S)) J).subscheme ⟶
      polynomialUniversalClosedFamily R I d)
    (hg : g ≫ polynomialUniversalClosedImmersion R I d =
      (baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
        polynomialFamilyAmbientMap R I d S J hd) :
    g = polynomialClosedFamilyMap R I d S J hd := by
  apply (cancel_mono (polynomialUniversalClosedImmersion R I d)).mp
  rw [polynomialClosedFamilyMap_immersion]
  exact hg

/-- The original closed family is the actual ambient pullback of the universal closed family. -/
theorem polynomialClosedFamilyMap_ambient_isPullback :
    IsPullback (baseIdeal (.of (MvPolynomial I S)) J).subschemeι
      (polynomialClosedFamilyMap R I d S J hd) (polynomialFamilyAmbientMap R I d S J hd)
      (polynomialUniversalClosedImmersion R I d) := by
  apply isPullback_of_isClosedImmersion _ _ _ _
    (polynomialClosedFamilyMap_immersion R I d S J hd).symm
  rw [ker_subschemeι]
  exact polynomialUniversalIdeal_familyPullback R I d S J hd

/-- The original closed family is the actual base change along its classifying parameter. -/
theorem polynomialClosedFamilyMap_isPullback :
    IsPullback (polynomialClosedFamilyMap R I d S J hd)
      ((baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))))
      (polynomialUniversalProjection R I d) (polynomialFamilyMorphism R I d S J hd) :=
  (polynomialClosedFamilyMap_ambient_isPullback R I d S J hd).flip.paste_vert
    (polynomialAmbientMap_isPullback R I d S _ (polynomialFamilyMorphism_over R I d S J hd))

end FLT.Mazur.HilbertChart
