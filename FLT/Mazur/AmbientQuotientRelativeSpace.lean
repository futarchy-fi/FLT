/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialRelativeAmbient
public import FLT.Mazur.BaseAdicQuotientSpectrum

/-!
# Actual quotient ambient spaces over arbitrary scheme bases

Base change the spectrum of the original polynomial quotient ring. Its
constructed map to relative polynomial space is the cartesian base change
of the original quotient-spectrum closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (K : Ideal (MvPolynomial I R))
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Cache the ambient quotient ring for actual spectrum maps. -/
local instance relativeQuotientRing : CommRing (MvPolynomial I R ⧸ K) := inferInstance

/-- Relative ambient space is the actual base change of the original affine quotient scheme. -/
def quotientRelativeAmbient : Scheme.{u} :=
  pullback s (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))

/-- The original quotient structure morphism factors through polynomial space. -/
theorem quotientAmbientStructure :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))) := by
  rw [← Spec.map_comp]
  rfl

/-- The actual ambient quotient base change embeds in relative polynomial space. -/
def quotientRelativeImmersion : quotientRelativeAmbient R I K s ⟶
    polynomialRelativeAmbient R I s :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) (by
      rw [Category.assoc, quotientAmbientStructure]
      exact pullback.condition)

/-- The relative quotient immersion respects the projection to the original base. -/
@[reassoc]
theorem quotientRelativeImmersion_fst :
    quotientRelativeImmersion R I K s ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The relative quotient immersion respects the original quotient polynomial coordinates. -/
@[reassoc]
theorem quotientRelativeImmersion_snd :
    quotientRelativeImmersion R I K s ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) :=
  pullback.lift_snd _ _ _

/-- The quotient relative immersion is precisely the base change of the original quotient map. -/
theorem quotientRelativeImmersion_isPullback :
    IsPullback (quotientRelativeImmersion R I K s) (pullback.snd _ _)
      (pullback.snd _ _) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := by
  have h : IsPullback (quotientRelativeImmersion R I K s ≫ pullback.fst _ _)
      (pullback.snd _ _) s
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I)))) := by
    rw [quotientRelativeImmersion_fst, quotientAmbientStructure]
    exact IsPullback.of_hasPullback _ _
  exact h.of_right (quotientRelativeImmersion_snd R I K s) (IsPullback.of_hasPullback _ _)

/-- The actual quotient relative ambient space is a closed subscheme of polynomial space. -/
instance quotientRelativeImmersion_isClosedImmersion :
    IsClosedImmersion (quotientRelativeImmersion R I K s) := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.of_isPullback (quotientRelativeImmersion_isPullback R I K s).flip
    (inferInstanceAs (IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))))

/-- The actual relative quotient immersion has precisely the full extended ambient ideal. -/
theorem quotientRelativeImmersion_ker :
    (quotientRelativeImmersion R I K s).ker =
      (baseIdeal (.of (MvPolynomial I R)) K).comap (pullback.snd _ _) := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let q := quotientRelativeImmersion_isPullback R I K s
  rw [← q.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact congrArg (fun J ↦ J.comap (pullback.snd s
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := R) (σ := I))))))
    (quotientSpec_ker (.of (MvPolynomial I R)) K)

end FLT.Mazur.HilbertChart
