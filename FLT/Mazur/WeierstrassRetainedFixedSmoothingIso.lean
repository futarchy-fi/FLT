/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedScalarSmoothingIso
public import FLT.Mazur.NilpotentAlgebraEquivalence

/-!
# Full nilpotent retained corrections are isomorphisms of entire charts

A correction reducing to one is a nilpotent perturbation of the explicit
scalar model. The constructed inverse includes both node coordinates and
all arithmetic orders; no punctured-branch inverse is used as a chart inverse.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π τ : R) (q α : Rˣ) (hq : π * (q : R) = τ)
  (I : Ideal R) (hI : IsNilpotent I) (V : (ChartRing π)ˣ)
  (hV : Units.map (Ideal.Quotient.mk (I.map (algebraMap R (ChartRing π)))).toMonoidHom V = 1)
local notation "J" => Ideal.map (algebraMap R (ChartRing π)) I
local notation "U" => retainedScaledCorrectionUnit π α V
local notation "E" => retainedFixedSmoothingEvaluation π τ (q : R) hq U
local notation "e" => retainedScalarSmoothingEquiv π τ q α hq
include hV

/-- The entire corrected map differs from the scalar equivalence only in the base ideal. -/
theorem retainedFixedSmoothingEvaluation_sub_scalar_mem (x : ChartRing τ) :
    E x - e x ∈ J := by
  let p := Ideal.Quotient.mkₐ R J
  have hv : p (V : ChartRing π) = 1 := congrArg Units.val hV
  have hi : p (↑V⁻¹ : ChartRing π) = 1 := by
    have hh := congrArg (fun z : (ChartRing π ⧸ J)ˣ ↦ (↑z⁻¹ : ChartRing π ⧸ J)) hV
    change p (↑V⁻¹ : ChartRing π) = (↑(1 : (ChartRing π ⧸ J)ˣ)⁻¹ : ChartRing π ⧸ J) at hh
    simpa only [inv_one, Units.val_one] using hh
  have he : p.comp E = p.comp (e).toAlgHom := by
    apply chartRing_hom_ext (S := ChartRing π ⧸ J) τ
    · change p (E (leftCoordinate τ)) = p (e (leftCoordinate τ))
      rw [retainedFixedSmoothingEvaluation_left, retainedScalarSmoothingEquiv_left]
      change p (algebraMap R _ (q : R) * leftCoordinate π *
          ((↑V⁻¹ : ChartRing π) * algebraMap R _ (↑α⁻¹ : R))) = _
      rw [map_mul, map_mul, map_mul, hi,
        one_mul (p (algebraMap R (ChartRing π) (↑α⁻¹ : R))), map_mul, map_mul]
    · change p (E (rightCoordinate τ)) = p (e (rightCoordinate τ))
      rw [retainedFixedSmoothingEvaluation_right, retainedScalarSmoothingEquiv_right]
      change p (rightCoordinate π * (algebraMap R _ (α : R) * (V : ChartRing π))) = _
      rw [map_mul, map_mul, hv, mul_one (p (algebraMap R (ChartRing π) (α : R))), map_mul]
  exact Ideal.Quotient.eq.mp (congrArg (fun f : ChartRing τ →ₐ[R] ChartRing π ⧸ J ↦ f x) he)

/-- The complete corrected evaluation has a constructed inverse. -/
def retainedFixedSmoothingEquiv : ChartRing τ ≃ₐ[R] ChartRing π :=
  NilpotentAlgebraEquivalence.equiv I hI e E
    (retainedFixedSmoothingEvaluation_sub_scalar_mem π τ q α hq I V hV)

/-- The full isomorphism retains precisely the original corrected evaluation. -/
theorem retainedFixedSmoothingEquiv_toAlgHom :
    (retainedFixedSmoothingEquiv π τ q α hq I hI V hV).toAlgHom = E := rfl

end FLT.Mazur.WeierstrassModificationX
