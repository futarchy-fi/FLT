/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFiniteRestrictionPaths

/-!
# Ambient coordinates for restriction-map descent

Coordinate recovery supplies the original restriction geometry. The second
localization denominator is exactly the image of the other chart numerator.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}

/-- An ambient finite-chart coordinate before the second localization. -/
def principalFanAmbient (x : PrincipalFanStage a b f) (i : ι) :
    Stage R A x.source →ₐ[R] PrincipalStage R (B i) (b i) (x.target i) :=
  (x.hom i).comp (Algebra.algHom R (Stage R A x.source)
    (PrincipalStage R A (a i) x.source))

/-- Ambient coordinates recover the original ambient restriction. -/
theorem principalFanAmbient_fac (x : PrincipalFanStage a b f) (i : ι) :
    (principalStageMap R (B i) (b i) (x.target i)).comp (principalFanAmbient x i) =
      ((f i).comp (Algebra.algHom R A (Localization.Away (a i)))).comp
        (stageMap R A x.source) := by
  rw [principalFanAmbient, ← AlgHom.comp_assoc, x.fac, AlgHom.comp_assoc]
  apply AlgHom.ext
  intro z
  exact congrArg (f i) (principalStageMap_algebraMap R A (a i) x.source z)

/-- Original ambient coordinates in the target's canonical localized presentation. -/
def principalFanOriginalAmbient (i : ι) : A →ₐ[R]
    FiniteRelationLocalization.Quotient (relationIdeal R (B i))
      (principalRepresentative R (B i) (b i)) :=
  (principalQuotientEquiv R (B i) (b i)).symm.toAlgHom.comp
    ((f i).comp (Algebra.algHom R A (Localization.Away (a i))))

/-- The finite ambient coordinate has exactly the prescribed original canonical map. -/
theorem principalFanAmbient_quotient (x : PrincipalFanStage a b f) (i : ι) :
    (FiniteRelationLocalization.toQuotient R (relationIdeal R (B i))
      (principalRepresentative R (B i) (b i)) (x.target i)).comp (principalFanAmbient x i) =
        (principalFanOriginalAmbient (f := f) i).comp (stageMap R A x.source) := by
  apply AlgHom.ext
  intro z
  apply (principalQuotientEquiv R (B i) (b i)).injective
  change principalStageMap R (B i) (b i) (x.target i) (principalFanAmbient x i z) =
    principalQuotientEquiv R (B i) (b i)
      ((principalQuotientEquiv R (B i) (b i)).symm
        (f i (algebraMap A (Localization.Away (a i)) (stageMap R A x.source z))))
  rw [AlgEquiv.apply_symm_apply]
  exact AlgHom.congr_fun (principalFanAmbient_fac x i) z

/-- The numerator image that defines the canonical finite restriction target. -/
abbrev principalFanRestrictionDenominator (x : PrincipalFanStage a b f) (i j : ι) :=
  principalFanAmbient x j (Ideal.Quotient.mk _ (principalRepresentative R A (a i)))

/-- Its projection is the original ambient image of the other principal denominator. -/
theorem principalFanRestrictionDenominator_spec (x : PrincipalFanStage a b f) (i j : ι) :
    principalFanOriginalAmbient (f := f) j (a i) =
      FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
          (principalFanRestrictionDenominator x i j) := by
  have h := AlgHom.congr_fun (principalFanAmbient_quotient x j)
    (Ideal.Quotient.mk _ (principalRepresentative R A (a i)))
  simpa only [AlgHom.comp_apply, stageMap_mk, principalRepresentative_spec] using h.symm

end FLT.Mazur.FiniteTypeRelationModel
