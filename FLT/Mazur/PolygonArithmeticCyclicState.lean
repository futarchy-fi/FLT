/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousState

/-!
# Full cyclic arithmetic correction data

Record every node and every edge, including the edge closing the initial pair.
Normalization and quotient compatibility are proved predicates, not state fields.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonScalingNaturality
open PolygonSmoothing LaurentPolynomial
variable (R : Type*) [CommRing R] (π : R) (ι : Type*)

/-- Actual node parameters and all full Laurent edge substitutions around a cycle. -/
structure State where
  /-- The smoothing of each entire node at every arithmetic order. -/
  parameter : (m : ℕ) → ι → Quotient R π m
  /-- The full substitution from a node's left puncture to its successor's right puncture. -/
  edge : (m : ℕ) → ι →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]

variable {R π ι}

/-- Every node and every complete edge respects the original quotient maps. -/
def State.Compatible (S : State R π ι) : Prop :=
  (∀ m i, restriction R π m (S.parameter (m + 1) i) = S.parameter m i) ∧
  ∀ i, CompatibleEquiv (fun m ↦ S.edge m i)

/-- The top arithmetic power annihilates every smoothing. -/
def State.Annihilated (S : State R π ι) : Prop :=
  ∀ m i, PolygonArithmeticStages.parameter R π m ^ m * S.parameter m i = 0

/-- All edges, including the closing edge, are the standard reciprocal substitution. -/
def State.Normalized (S : State R π ι) (m : ℕ) : Prop :=
  ∀ i, S.edge m i = invert

/-- Measure the entire edge relative to the standard reciprocal substitution. -/
def State.error (S : State R π ι) (i : ι) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (S.edge m i).trans invert.symm

/-- The measured edge retains its full coefficient square. -/
theorem State.error_compatible (S : State R π ι) (hS : S.Compatible) (i : ι) :
    CompatibleEquiv (S.error i) := by
  intro m
  apply punctureEquiv_trans_naturality
  · exact hS.2 i m
  · exact LaurentUnitSubstitutionNaturality.symm_naturality _ _ _
      (punctureEquiv_invert_naturality _)

/-- A normalized edge has identity full relative error. -/
theorem State.error_normalized (S : State R π ι) (r : ℕ)
    (hr : S.Normalized r) (i : ι) : S.error i r = AlgEquiv.refl := by
  unfold State.error
  rw [hr i]
  ext z : 1
  exact invert.symm_apply_apply z

/-- Full normalization descends through arbitrary earlier quotients. -/
theorem State.normalized_restriction (S : State R π ι) (hS : S.Compatible)
    {k m : ℕ} (hkm : k ≤ m) (hm : S.Normalized m) : S.Normalized k := by
  intro i
  have he := laurentSystem_identity_restriction (fun j ↦ (S.error i j).toAlgHom)
    (S.error_compatible hS i) hkm
    (congrArg AlgEquiv.toAlgHom (S.error_normalized m hm i))
  ext z : 1
  apply invert.symm.injective
  exact (DFunLike.congr_fun he z).trans (invert.symm_apply_apply z).symm

/-- Extract the entire next error field from the actual compatible edge. -/
def State.nextField (S : State R π ι) (hS : S.Compatible)
    (r : ℕ) (hr : S.Normalized r) (i : ι) : (Quotient R π (r + 1))[T;T⁻¹] :=
  laurentSystemNextField (fun m ↦ (S.error i m).toAlgHom)
    (S.error_compatible hS i) r (congrArg AlgEquiv.toAlgHom (S.error_normalized r hr i))

/-- The field represents the whole next substitution, with no discarded coefficients. -/
theorem State.nextField_subst (S : State R π ι) (hS : S.Compatible)
    (r : ℕ) (hr : S.Normalized r) (i : ι) :
    (S.error i (r + 1)).toAlgHom =
      LaurentSquareZeroAutomorphism.subst (PolygonArithmeticStages.parameter R π (r + 1) ^
        (r + 1)) (nextCorrectionParameter_square R π r) (S.nextField hS r hr i) :=
  laurentSystemNextField_subst (fun m ↦ (S.error i m).toAlgHom)
    (S.error_compatible hS i) r (congrArg AlgEquiv.toAlgHom (S.error_normalized r hr i))

/-- Choose one integral field per edge before choosing a target arithmetic order. -/
def State.nextIntegralField (S : State R π ι) (hS : S.Compatible)
    (r : ℕ) (hr : S.Normalized r) (i : ι) : R[T;T⁻¹] :=
  integralCorrectionLift R π (r + 1) (S.nextField hS r hr i)

/-- Every integral field recovers the full measured next error. -/
theorem State.nextIntegralField_spec (S : State R π ι) (hS : S.Compatible)
    (r : ℕ) (hr : S.Normalized r) (i : ι) :
    correctionField R π (r + 1) (S.nextIntegralField hS r hr i) =
      S.nextField hS r hr i := integralCorrectionLift_spec R π _ _

end FLT.Mazur.PolygonArithmeticCyclic
