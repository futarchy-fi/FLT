/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineLinearTransport
public import FLT.Mazur.FiniteFreeDualProjectivePoints
public import FLT.Mazur.ProjectiveSectionLineChart

/-!
# Section lines under genuine dual projective coordinate changes

The finite free coordinate transition acts on actual section submodules by
its original linear map. The corresponding line sheaf inclusion and actual
projective scheme point transform by the same change of coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeContragredient
open NormalizedSectionLine ProjectiveSpace
variable {R : Type u} [CommRing R] {ι κ : Type u} [Finite ι] [Finite κ]

/-- The original finite free coordinate map on vectors with all coordinates present. -/
def functionCoordinates (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    (ι → R) ≃ₗ[R] (κ → R) :=
  (Finsupp.linearEquivFunOnFinite R R ι).symm.trans
    (e.trans (Finsupp.linearEquivFunOnFinite R R κ))

/-- Conversion to ordinary functions preserves composition of section coordinates. -/
lemma functionCoordinates_trans {ν : Type u} [Finite ν]
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (d : (κ →₀ R) ≃ₗ[R] (ν →₀ R)) :
    functionCoordinates (e.trans d) = (functionCoordinates e).trans (functionCoordinates d) := by
  ext v j
  simp only [functionCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- Conversion to ordinary functions preserves the identity coordinate change. -/
lemma functionCoordinates_refl :
    functionCoordinates (LinearEquiv.refl R (ι →₀ R)) = LinearEquiv.refl R (ι → R) := by
  ext v j
  simp only [functionCoordinates, LinearEquiv.trans_apply, LinearEquiv.refl_apply,
    LinearEquiv.apply_symm_apply]

/-- Conversion to ordinary functions preserves the inverse coordinate change. -/
lemma functionCoordinates_symm (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) :
    functionCoordinates e.symm = (functionCoordinates e).symm := rfl

/-- The actual section line point transforms by the dual projective isomorphism. -/
lemma sectionLinePoint_linearTransport (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (i : ι) (j : κ) (L : Chart R ι i) (a : Rˣ)
    (ha : functionCoordinates e (generator R ι i L) j = a) :
    sectionLinePoint R ι (.id R) i L ≫ (linearIso (map e)).hom =
      sectionLinePoint R κ (.id R) j
        (linearTransport (functionCoordinates e) i j L a ha) := by
  rw [sectionLinePoint_eq_unitChartPoint, sectionLinePoint_eq_unitChartPoint]
  let v := (Finsupp.linearEquivFunOnFinite R R ι).symm (generator R ι i L)
  have hi : v i = (1 : Rˣ) := generator_coordinate R ι i L
  have hj : e v j = a := ha
  have hv : (fun k ↦ v k) = generator R ι i L :=
    (Finsupp.linearEquivFunOnFinite R R ι).apply_symm_apply _
  trans unitChartPoint R κ (.id R) (fun k ↦ e v k) j a hj
  · simpa only [hv] using unitChartPoint_transport e v i j 1 a hi hj
  have hfun : functionCoordinates e (generator R ι i L) = fun k ↦ e v k := by
    funext k
    rfl
  have hs := unitChartPoint_scale R κ (.id R) (fun k ↦ e v k) j a a⁻¹ hj
  simpa only [generator_linearTransport, hfun, inv_mul_cancel, Pi.smul_def, smul_eq_mul]
    using hs.symm

end FLT.Mazur.FiniteFreeContragredient
