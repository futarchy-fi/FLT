/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSeparatedDifferentials
public import FLT.Mazur.DerivationAlgEquivTransport

/-!
# Maps of completed original differentials under formal algebra maps

The derivative of a formal algebra map factors through the completed
original differential module, without requiring that map to be invertible.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCotangentHomMap

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsNoetherianRing A] [Module.Finite A Ω[A⁄R]]
  (I : Ideal A) (J : Ideal B) (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)

/-- A formal algebra map acts on completed original differentials. -/
def map : AdicCompletion I Ω[A⁄R] →ₛₗ[e.toRingHom] AdicCompletion J Ω[B⁄R] := by
  let N := AdicCompletion J Ω[B⁄R]
  let _ : Module (AdicCompletion I A) N := Module.compHom N e.toRingHom
  let _ : Module A N := Module.compHom N (algebraMap A (AdicCompletion I A))
  let _ : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (algebraMap R (AdicCompletion I A) r) • x = r • x
      rw [e.commutes, algebraMap_smul]
  let _ : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change e (algebraMap A (AdicCompletion I A) (algebraMap R A r)) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R A (AdicCompletion I A),
      e.commutes, algebraMap_smul]
  let d := DerivationAlgEquivTransport.pullback e (fun _ _ ↦ rfl)
    (AdicDerivationFiltration.completion (KaehlerDifferential.D R B) J)
  let f := AdicSeparatedDifferentials.lift I d
  exact { f.toAddHom with map_smul' := fun a x ↦ f.map_smul a x }

/-- On original differentials this is the derivative of the actual image of the section. -/
theorem map_of_D (a : A) :
    map I J e (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a)) =
      AdicDerivationFiltration.completion (KaehlerDifferential.D R B) J
        (e (AdicCompletion.of I A a)) := by
  let N := AdicCompletion J Ω[B⁄R]
  let _ : Module (AdicCompletion I A) N := Module.compHom N e.toRingHom
  let _ : Module A N := Module.compHom N (algebraMap A (AdicCompletion I A))
  let _ : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change e (algebraMap R (AdicCompletion I A) r) • x = r • x
      rw [e.commutes, algebraMap_smul]
  let _ : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change e (algebraMap A (AdicCompletion I A) (algebraMap R A r)) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R A (AdicCompletion I A),
      e.commutes, algebraMap_smul]
  change AdicSeparatedDifferentials.lift I
    (DerivationAlgEquivTransport.pullback e (fun _ _ ↦ rfl)
      (AdicDerivationFiltration.completion (KaehlerDifferential.D R B) J)) _ = _
  rw [AdicSeparatedDifferentials.lift_of_D]
  rfl

end FLT.Mazur.AdicCotangentHomMap
