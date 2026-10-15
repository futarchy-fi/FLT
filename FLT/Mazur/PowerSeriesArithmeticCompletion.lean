/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import FLT.Mazur.AdicCompletionPositiveLimit

/-!
# The integral power-series map to the arithmetic completion

Compatible finite evaluations construct a map from A[[t]] to the π-adic
completion of A, retaining the original constants and sending t to π.
For a complete arithmetic ring this gives a surjective map to A itself.
No map from the residue coefficient field to A is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
variable (A : Type*) [CommRing A] (π : A)

/-- The actual finite evaluations, viewed as compatible positive-power sections. -/
def specializationSections :
    PowerSeries A →+* AdicCompletionPositiveLimit.sections (ideal A π) where
  toFun f := ⟨fun m ↦ seriesSpecialization A π m f, fun hab ↦
    DFunLike.congr_fun (seriesSpecialization_compatible A π hab) f⟩
  map_zero' := Subtype.ext (funext fun m ↦ map_zero (seriesSpecialization A π m))
  map_one' := Subtype.ext (funext fun m ↦ map_one (seriesSpecialization A π m))
  map_add' f g := Subtype.ext (funext fun m ↦ map_add (seriesSpecialization A π m) f g)
  map_mul' f g := Subtype.ext (funext fun m ↦ map_mul (seriesSpecialization A π m) f g)

/-- The reconstructed ring map to the completion of the original integral base. -/
def completionSpecializationRing : PowerSeries A →+* AdicCompletion (ideal A π) A :=
  (AdicCompletionPositiveLimit.fromSections (ideal A π)).comp (specializationSections A π)

/-- Reconstruction retains every original finite arithmetic evaluation. -/
@[simp] theorem completionSpecializationRing_stage (m : ℕ) (f : PowerSeries A) :
    AdicCompletion.evalₐ (ideal A π) (m + 1) (completionSpecializationRing A π f) =
      seriesSpecialization A π m f :=
  AdicCompletionPositiveLimit.eval_fromSections _ _ _

/-- The reconstructed map preserves the original arithmetic constants. -/
theorem completionSpecializationRing_constant (a : A) :
    completionSpecializationRing A π (PowerSeries.C a) =
      algebraMap A (AdicCompletion (ideal A π) A) a := by
  apply (AdicCompletionPositiveLimit.equivalence (ideal A π)).injective
  apply Subtype.ext
  funext m
  change AdicCompletion.evalₐ _ (m + 1) (completionSpecializationRing A π _) = _
  rw [completionSpecializationRing_stage]
  exact (seriesSpecialization A π m).commutes a

/-- The integral coefficient map, with its original A-algebra structure. -/
def completionSpecialization : PowerSeries A →ₐ[A] AdicCompletion (ideal A π) A where
  __ := completionSpecializationRing A π
  commutes' := completionSpecializationRing_constant A π

/-- The power-series variable maps to the original π in the arithmetic completion. -/
@[simp] theorem completionSpecialization_X :
    completionSpecialization A π PowerSeries.X =
      algebraMap A (AdicCompletion (ideal A π) A) π := by
  apply (AdicCompletionPositiveLimit.equivalence (ideal A π)).injective
  apply Subtype.ext
  funext m
  change AdicCompletion.evalₐ _ (m + 1) (completionSpecializationRing A π _) = _
  rw [completionSpecializationRing_stage, seriesSpecialization_X]
  exact ((AdicCompletion.evalₐ (ideal A π) (m + 1)).commutes π).symm

variable [IsAdicComplete (ideal A π) A]

/-- Over a complete integral base, evaluation at π lands in the original ring itself. -/
def completeSpecialization : PowerSeries A →ₐ[A] A :=
  (AdicCompletion.ofAlgEquiv (ideal A π)).symm.toAlgHom.comp (completionSpecialization A π)

/-- The complete evaluation retains the original parameter. -/
@[simp] theorem completeSpecialization_X : completeSpecialization A π PowerSeries.X = π := by
  rw [completeSpecialization, AlgHom.comp_apply, completionSpecialization_X,
    AlgEquiv.coe_toAlgHom, AlgEquiv.commutes]
  rfl

/-- The actual quotient of the complete evaluation is the original finite evaluation. -/
@[simp] theorem completeSpecialization_stage (m : ℕ) (f : PowerSeries A) :
    Ideal.Quotient.mk (ideal A π ^ (m + 1)) (completeSpecialization A π f) =
      seriesSpecialization A π m f := by
  change Ideal.Quotient.mk _ ((AdicCompletion.ofAlgEquiv _).symm _) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm]
  exact completionSpecializationRing_stage A π m f

/-- Constants split the complete evaluation, so the integral base map is surjective. -/
theorem completeSpecialization_surjective : Function.Surjective (completeSpecialization A π) :=
  fun a ↦ ⟨PowerSeries.C a, (completeSpecialization A π).commutes a⟩

end FLT.Mazur.PolygonArithmeticStages
