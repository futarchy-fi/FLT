/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
public import FLT.Mazur.HilbertPolynomialSchemeParameterIdeal
public import FLT.Mazur.HilbertPolynomialUniversalDegree

/-!
# Finite locally free closed families of arbitrary scheme parameters

Every scheme parameter gives an actual closed family in its relative
polynomial space. The family is cartesian over the universal projection and
has finite locally free degree exactly `d`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (f : X ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d = s)

/-- The actual closed family maps to the universal family over its ambient parameter. -/
def polynomialSchemeParameterClosedMap : (polynomialSchemeParameterIdeal R I d s f hf).subscheme ⟶
    polynomialUniversalClosedFamily R I d :=
  IsClosedImmersion.lift (polynomialUniversalClosedImmersion R I d)
    ((polynomialSchemeParameterIdeal R I d s f hf).subschemeι ≫
      polynomialRelativeAmbientMap R I (polynomialHilbertStructure R I d) s f hf) (by
      rw [← map_bot ((polynomialSchemeParameterIdeal R I d s f hf).subschemeι ≫
        polynomialRelativeAmbientMap R I (polynomialHilbertStructure R I d) s f hf),
        le_map_iff_comap_le]
      change (polynomialUniversalIdeal R I d).comap _ ≤ ⊥
      rw [comap_comp,
        ← polynomialSchemeParameterIdeal,
        ClosedIdealCover.comap_subschemeι_eq_bot])

/-- The family map preserves its original closed immersion in the polynomial ambient space. -/
@[reassoc]
theorem polynomialSchemeParameterClosedMap_immersion :
    polynomialSchemeParameterClosedMap R I d s f hf ≫ polynomialUniversalClosedImmersion R I d =
      (polynomialSchemeParameterIdeal R I d s f hf).subschemeι ≫
        polynomialRelativeAmbientMap R I (polynomialHilbertStructure R I d) s f hf :=
  IsClosedImmersion.lift_fac _ _ _

/-- The closed-family comparison is uniquely determined by its ambient compatibility. -/
theorem polynomialSchemeParameterClosedMap_unique
    (g : (polynomialSchemeParameterIdeal R I d s f hf).subscheme ⟶
      polynomialUniversalClosedFamily R I d)
    (hg : g ≫ polynomialUniversalClosedImmersion R I d =
      (polynomialSchemeParameterIdeal R I d s f hf).subschemeι ≫
        polynomialRelativeAmbientMap R I (polynomialHilbertStructure R I d) s f hf) :
    g = polynomialSchemeParameterClosedMap R I d s f hf := by
  apply (cancel_mono (polynomialUniversalClosedImmersion R I d)).mp
  rw [polynomialSchemeParameterClosedMap_immersion]
  exact hg

/-- The original closed family is the actual ambient pullback of the universal closed family. -/
theorem polynomialSchemeParameterClosedMap_ambient_isPullback :
    IsPullback (polynomialSchemeParameterIdeal R I d s f hf).subschemeι
      (polynomialSchemeParameterClosedMap R I d s f hf)
      (polynomialRelativeAmbientMap R I (polynomialHilbertStructure R I d) s f hf)
      (polynomialUniversalClosedImmersion R I d) := by
  apply isPullback_of_isClosedImmersion _ _ _ _
    (polynomialSchemeParameterClosedMap_immersion R I d s f hf).symm
  rw [ker_subschemeι]
  rfl

/-- The original closed family is the actual base change along its classifying parameter. -/
theorem polynomialSchemeParameterClosedMap_isPullback :
    IsPullback (polynomialSchemeParameterClosedMap R I d s f hf)
      ((polynomialSchemeParameterIdeal R I d s f hf).subschemeι ≫
        pullback.fst _ _)
      (polynomialUniversalProjection R I d) f :=
  (polynomialSchemeParameterClosedMap_ambient_isPullback R I d s f hf).flip.paste_vert
    (polynomialRelativeAmbientMap_isPullback R I (polynomialHilbertStructure R I d) s f hf)

/-- The actual closed family of every scheme parameter has the prescribed finite flat degree. -/
theorem polynomialSchemeParameterIdeal_degree :
    FiniteLocallyFreeDegree ((polynomialSchemeParameterIdeal R I d s f hf).subschemeι ≫
      pullback.fst _ _) d :=
  finiteLocallyFreeDegree_of_isPullback
    (polynomialSchemeParameterClosedMap_isPullback R I d s f hf) d
    (polynomialUniversalProjection_degree R I d)

end FLT.Mazur.HilbertChart
