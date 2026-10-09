/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientSchemeNaturality

/-!
# The actual universal family in the affine quotient ambient

The identity parameter gives the universal closed ideal inside the actual
quotient ambient base change. Its projection is finite locally free of the
specified degree, and every represented family is its full ideal pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))

/-- The actual universal quotient-ambient family is the family of the identity parameter. -/
def ambientUniversalFamily :
    QuotientSchemeFamilies R I d K (ambientHilbertStructure R I d K) :=
  ambientSchemeClassification R I d K (ambientHilbertStructure R I d K)
    ⟨𝟙 _, Category.id_comp _⟩

/-- The full universal ideal inside the actual quotient ambient over its parameter scheme. -/
def ambientUniversalIdeal :
    (quotientRelativeAmbient R I K (ambientHilbertStructure R I d K)).IdealSheafData :=
  (ambientUniversalFamily R I d K).val

/-- The actual universal closed family projects to the actual ambient Hilbert parameter scheme. -/
def ambientUniversalProjection : (ambientUniversalIdeal R I d K).subscheme ⟶
    ambientHilbertScheme R I d K :=
  (ambientUniversalIdeal R I d K).subschemeι ≫ pullback.fst _ _

/-- The constructed universal quotient-ambient family has exactly finite locally free degree d. -/
theorem ambientUniversalProjection_degree :
    FCurve.FiniteLocallyFreeDegree (ambientUniversalProjection R I d K) d :=
  (ambientUniversalFamily R I d K).property

/-- Every actual represented family is the pullback of the entire universal quotient ideal. -/
theorem ambientSchemeClassification_universalPullback
    {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (f : AmbientSchemeParameters R I d K s) :
    (ambientUniversalIdeal R I d K).comap
        (quotientRelativeAmbientMap R I K (ambientHilbertStructure R I d K) s f.val f.property) =
      (ambientSchemeClassification R I d K s f).val := by
  have h := ambientSchemeClassification_natural R I d K
    (ambientHilbertStructure R I d K) s f.val f.property ⟨𝟙 _, Category.id_comp _⟩
  have he : ambientSchemeParameterBaseChange R I d K
      (ambientHilbertStructure R I d K) s f.val f.property ⟨𝟙 _, Category.id_comp _⟩ = f := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [he] at h
  exact (congrArg Subtype.val h).symm

end FLT.Mazur.HilbertChart
