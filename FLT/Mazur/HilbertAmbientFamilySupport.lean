/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFamilySupportBaseChange
public import FLT.Mazur.HilbertAmbientUniversalFamily

/-!
# Exact support loci for actual affine quotient ambient families

For an open in the original affine ambient, remove the finite image of the
actual closed family's complement in that open. The support locus commutes
with arbitrary base change and defines an actual open of the ambient Hilbert
scheme by applying the construction to its universal family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (J : QuotientSchemeFamilies R I d K s)
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)

/-- The actual closed family maps to the original affine ambient quotient spectrum. -/
def quotientFamilyAmbientMap : J.val.subscheme ⟶ Spec (.of (MvPolynomial I R ⧸ K)) :=
  J.val.subschemeι ≫ pullback.snd _ _

/-- Remove the finite image of the family's actual complement in the given ambient open. -/
def quotientFamilySupportOpen : X.Opens := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst _ _) := J.property.1
  exact finiteFamilySupportOpen (J.val.subschemeι ≫ pullback.fst _ _)
    (quotientFamilyAmbientMap R I d K s J ⁻¹ᵁ U)

/-- The support open is exactly where the full actual family lies in the chosen ambient open. -/
theorem mem_quotientFamilySupportOpen (x : X) :
    x ∈ quotientFamilySupportOpen R I d K s J U ↔
      ∀ z : J.val.subscheme, (J.val.subschemeι ≫ pullback.fst _ _) z = x →
        quotientFamilyAmbientMap R I d K s J z ∈ U := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst _ _) := J.property.1
  exact mem_finiteFamilySupportOpen _ _ x

/-- The actual pulled-back family preserves its morphism into the original quotient ambient. -/
theorem quotientFamilyAmbientMap_baseChange (t : Y ⟶ Spec (.of R))
    (g : Y ⟶ X) (hg : g ≫ s = t) :
    restrictionMap J.val (quotientRelativeAmbientMap R I K s t g hg) ≫
        quotientFamilyAmbientMap R I d K s J =
      quotientFamilyAmbientMap R I d K t (quotientSchemeFamilyBaseChange R I d K s t g hg J) := by
  unfold quotientFamilyAmbientMap
  rw [← Category.assoc, restrictionMap_immersion, Category.assoc,
    quotientRelativeAmbientMap_snd]
  rfl

/-- Full finite-family support loci commute with arbitrary scheme base change. -/
theorem quotientFamilySupportOpen_baseChange (t : Y ⟶ Spec (.of R))
    (g : Y ⟶ X) (hg : g ≫ s = t) :
    quotientFamilySupportOpen R I d K t (quotientSchemeFamilyBaseChange R I d K s t g hg J) U =
      g ⁻¹ᵁ quotientFamilySupportOpen R I d K s J U := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst _ _) := J.property.1
  let J' := quotientSchemeFamilyBaseChange R I d K s t g hg J
  let _ : IsFinite (J'.val.subschemeι ≫ pullback.fst _ _) := J'.property.1
  have h := finiteFamilySupportOpen_baseChange (J.val.subschemeι ≫ pullback.fst _ _)
    (quotientFamilyAmbientMap R I d K s J ⁻¹ᵁ U)
    (restrictionMap J.val (quotientRelativeAmbientMap R I K s t g hg))
    (J'.val.subschemeι ≫ pullback.fst _ _) g
    (restrictionMap_base_isPullback J.val _
      (quotientRelativeAmbientMap_isPullback R I K s t g hg))
  rw [← Scheme.Hom.comp_preimage, quotientFamilyAmbientMap_baseChange] at h
  exact h

/-- The actual Hilbert parameter open whose universal family is supported in the ambient open. -/
def ambientHilbertSupportOpen : (ambientHilbertScheme R I d K).Opens :=
  quotientFamilySupportOpen R I d K (ambientHilbertStructure R I d K)
    (ambientUniversalFamily R I d K) U

end FLT.Mazur.HilbertChart
