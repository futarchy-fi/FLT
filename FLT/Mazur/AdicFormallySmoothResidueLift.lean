/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormallySmoothLift

/-!
# Lifting smooth points through an actual complete coefficient quotient

The residue algebra is retained as given. The quotient-kernel comparison
transports the constructed complete lift back to the original reduction map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicFormallySmoothResidueLift
set_option backward.isDefEq.respectTransparency false
universe u
variable {R B K : Type u} [CommRing R] [CommRing B] [CommRing K]
  [Algebra R B] [Algebra R K] [Algebra.FormallySmooth R B]
  (h : Function.Surjective (algebraMap R K))

/-- The quotient comparison for the actual structural algebra map. -/
def residueEquiv : (R ⧸ RingHom.ker (algebraMap R K)) ≃ₐ[R] K :=
  Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom R R K) h

/-- The quotient comparison retains the given structural reduction map. -/
theorem residueEquiv_mk (r : R) :
    residueEquiv h (Ideal.Quotient.mk _ r) = algebraMap R K r := rfl

variable [IsAdicComplete (RingHom.ker (algebraMap R K)) R] (f : B →ₐ[R] K)

/-- The original residue point lifted over the unchanged complete coefficient ring. -/
def lift : B →ₐ[R] R :=
  AdicFormallySmoothLift.closedLift (RingHom.ker (algebraMap R K))
    ((residueEquiv h).symm.toAlgHom.comp f)

/-- Reducing the constructed point recovers every original residue coordinate. -/
theorem reduction_lift (b : B) : algebraMap R K (lift h f b) = f b := by
  have he := congrArg (residueEquiv h)
    (AdicFormallySmoothLift.quotient_closedLift (RingHom.ker (algebraMap R K))
      ((residueEquiv h).symm.toAlgHom.comp f) b)
  simpa only [lift, residueEquiv_mk,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using he

/-- The entire original reduction map is retained by the lift. -/
theorem reduction_comp_lift : (IsScalarTower.toAlgHom R R K).comp (lift h f) = f :=
  AlgHom.ext (reduction_lift h f)

include h in
/-- Every point of a formally smooth algebra over a complete quotient extends. -/
theorem exists_lift : ∃ g : B →ₐ[R] R, (IsScalarTower.toAlgHom R R K).comp g = f :=
  ⟨lift h f, reduction_comp_lift h f⟩

end FLT.Mazur.AdicFormallySmoothResidueLift
