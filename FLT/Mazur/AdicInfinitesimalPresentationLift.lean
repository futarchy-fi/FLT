/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicPolynomialPresentationLift
public import FLT.Mazur.AdicExtensionProjectionKernel
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Formal lifts of original infinitesimal presentations

The completed target infinitesimal extension has square-zero kernel.
Therefore the constructed polynomial lift kills the square of the original
relation ideal and descends to the original infinitesimal presentation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalPresentationLift

open AdicExtensionProjection AdicPolynomialPresentationLift

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B ι : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension.{u} R B) [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)

/-- The actual completed infinitesimal presentation has square-zero kernel. -/
theorem square_zero :
    (RingHom.ker (projection Q.infinitesimal J).toRingHom) ^ 2 = ⊥ := by
  let _ : IsNoetherianRing Q.infinitesimal.Ring :=
    inferInstanceAs (IsNoetherianRing (Q.Ring ⧸ Q.ker ^ 2))
  apply ker_projection_square_zero
  rw [Algebra.Extension.ker_infinitesimal, Ideal.cotangentIdeal_square]

/-- The constructed formal polynomial lift annihilates original relation squares. -/
theorem relation_square_le_ker :
    P.ker ^ 2 ≤ RingHom.ker (lift P Q.infinitesimal I J e).toRingHom := by
  have hk : P.ker.map (lift P Q.infinitesimal I J e).toRingHom ≤
      RingHom.ker (projection Q.infinitesimal J).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact relation_maps_to_kernel P Q.infinitesimal I J e ⟨x, hx⟩
  apply (Ideal.map_eq_bot_iff_le_ker _).mp
  apply le_antisymm _ bot_le
  rw [Ideal.map_pow]
  exact (pow_le_pow_left' hk 2).trans_eq (square_zero Q J)

/-- A formal map lifts to the original square-zero presentation, with no lifting hypothesis. -/
def infinitesimalLift : P.toExtension.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring :=
  Ideal.Quotient.liftₐ (P.ker ^ 2) (lift P Q.infinitesimal I J e)
    (fun _ hx ↦ relation_square_le_ker P Q I J e hx)

/-- The descended lift agrees with the original polynomial lift on every polynomial class. -/
theorem infinitesimalLift_mk (x : P.Ring) :
    infinitesimalLift P Q I J e (Ideal.Quotient.mk (P.ker ^ 2) x) =
      lift P Q.infinitesimal I J e x := rfl

/-- The descended lift still lies over the given formal comparison. -/
theorem projection_infinitesimalLift (x : P.toExtension.infinitesimal.Ring) :
    projection Q.infinitesimal J (infinitesimalLift P Q I J e x) =
      e (algebraMap A (AdicCompletion I A)
        (algebraMap P.toExtension.infinitesimal.Ring A x)) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact projection_lift P Q.infinitesimal I J e x

end FLT.Mazur.AdicInfinitesimalPresentationLift
