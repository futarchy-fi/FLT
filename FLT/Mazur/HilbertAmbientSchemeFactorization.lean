/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientContainmentTest
public import FLT.Mazur.HilbertAmbientParameterChart
public import FLT.Mazur.HilbertAmbientParameterCover
public import FLT.Mazur.IdealSheafOpenCoverDetection

/-!
# Exact closed ambient factorization over arbitrary schemes

The global closed equation ideal vanishes on a scheme parameter exactly
when its full actual family lies in the actual affine quotient ambient.
Both sides are checked on constructed affine refinements, including all
nonreduced structure, with no local factorization hypothesis in the result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (f : X ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d = s)

/-- The constructed affine parameter cover identifies equation vanishing with actual containment. -/
theorem ambientHilbertFactorization_coverTest
    (i : (ambientParameterAffineCover R I d f).I₀) :
    ((ambientHilbertIdeal R I d K).comap f).comap
        ((ambientParameterAffineCover R I d f).f i) = ⊥ ↔
      ((quotientRelativeImmersion R I K s).ker).comap
          (polynomialAffineCoverChart R I s (ambientParameterAffineCover R I d f) i) ≤
        (polynomialSchemeParameterIdeal R I d s f hf).comap
          (polynomialAffineCoverChart R I s (ambientParameterAffineCover R I d f) i) := by
  let C := ambientParameterAffineCover R I d f
  let _ := polynomialAffineCoverAlgebra R s C i
  let b := ambientParameterCoverAlgHom R I d s f hf i
  have hb : C.f i ≫ f =
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ polynomialHilbertChartι R I d i.1 := by
    rw [ambientParameterCoverAlgHom_spec]
    exact ambientParameterCoverChart_factor R I d f i
  rw [← Scheme.IdealSheafData.comap_comp, hb,
    ambientHilbertIdeal_affineChart_eq_bot_iff]
  exact (ambientContainment_affineTest_iff R I d K s (C.X i) (C.f i)
    (polynomialAffineCoverAlgebra_over R s C i) f hf i.1 b hb).symm

/-- Exact ambient containment is equivalent to global closed equation vanishing on any scheme. -/
theorem ambientHilbertIdeal_eq_bot_iff :
    (ambientHilbertIdeal R I d K).comap f = ⊥ ↔
      (quotientRelativeImmersion R I K s).ker ≤ polynomialSchemeParameterIdeal R I d s f hf := by
  rw [idealSheaf_eq_bot_iff_openCover (ambientParameterAffineCover R I d f).openCover,
    idealSheaf_le_iff_openCover
      (polynomialAffineCoverExtension R I s (ambientParameterAffineCover R I d f))]
  constructor
  · intro h i
    exact (ambientHilbertFactorization_coverTest R I d K s f hf i).mp (h i)
  · intro h i
    exact (ambientHilbertFactorization_coverTest R I d K s f hf i).mpr (h i)

/-- The full family containment gives the actual kernel inclusion for the parameter immersion. -/
theorem ambientHilbertIdeal_le_parameterKer
    (h : (quotientRelativeImmersion R I K s).ker ≤
      polynomialSchemeParameterIdeal R I d s f hf) :
    (ambientHilbertι R I d K).ker ≤ f.ker := by
  have he := (ambientHilbertIdeal_eq_bot_iff R I d K s f hf).mpr h
  have hl := (Scheme.IdealSheafData.le_map_iff_comap_le
    (I := (⊥ : X.IdealSheafData)) (f := f) (J := ambientHilbertIdeal R I d K)).mpr he.le
  simpa only [Scheme.IdealSheafData.map_bot, ambientHilbertIdeal] using hl

/-- Every contained family parameter factors through the constructed ambient Hilbert scheme. -/
def ambientSchemeParameterLift
    (h : (quotientRelativeImmersion R I K s).ker ≤
      polynomialSchemeParameterIdeal R I d s f hf) : X ⟶ ambientHilbertScheme R I d K :=
  IsClosedImmersion.lift (ambientHilbertι R I d K) f
    (ambientHilbertIdeal_le_parameterKer R I d K s f hf h)

/-- The constructed global lift recovers the original polynomial Hilbert parameter. -/
@[reassoc]
theorem ambientSchemeParameterLift_ι
    (h : (quotientRelativeImmersion R I K s).ker ≤
      polynomialSchemeParameterIdeal R I d s f hf) :
    ambientSchemeParameterLift R I d K s f hf h ≫ ambientHilbertι R I d K = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The ambient lift retains the original scheme's coefficient structure morphism. -/
theorem ambientSchemeParameterLift_over
    (h : (quotientRelativeImmersion R I K s).ker ≤
      polynomialSchemeParameterIdeal R I d s f hf) :
    ambientSchemeParameterLift R I d K s f hf h ≫ ambientHilbertStructure R I d K = s := by
  rw [ambientHilbertStructure, ← Category.assoc, ambientSchemeParameterLift_ι, hf]

end FLT.Mazur.HilbertChart
