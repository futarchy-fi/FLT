/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentHomMap

/-!
# Differentiating filtered formal algebra maps

Containment of the extended original ideals gives the target separation
needed to differentiate a formal algebra map on every completed section.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCotangentHomMap

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsNoetherianRing A] [Module.Finite A Ω[A⁄R]]
  (I : Ideal A) (J : Ideal B) (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)

/-- The cotangent map differentiates the filtered algebra map on all completed sections. -/
theorem map_completed
    (he : (I.map (algebraMap A (AdicCompletion I A))).map e.toRingHom ≤
      J.map (algebraMap B (AdicCompletion J B))) (a : AdicCompletion I A) :
    map I J e (AdicDerivationFiltration.completion (KaehlerDifferential.D R A) I a) =
      AdicDerivationFiltration.completion (KaehlerDifferential.D R B) J (e a) := by
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
  let _ : Algebra A (AdicCompletion J B) :=
    (e.toRingHom.comp (algebraMap A (AdicCompletion I A))).toAlgebra
  let _ : IsScalarTower A (AdicCompletion J B) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hI : I.map (algebraMap A (AdicCompletion J B)) ≤
      J.map (algebraMap B (AdicCompletion J B)) := by
    change I.map (e.toRingHom.comp (algebraMap A (AdicCompletion I A))) ≤ _
    rw [← Ideal.map_map]
    exact he
  let _ : IsHausdorff I N := by
    let _ : IsHausdorff (J.map (algebraMap B (AdicCompletion J B))) N :=
      (IsHausdorff.map_algebraMap_iff (S := AdicCompletion J B) (I := J)).mpr inferInstance
    exact IsHausdorff.of_map hI
  have hd := Derivation.congr_fun (AdicSeparatedDifferentials.lift_comp I
    (DerivationAlgEquivTransport.pullback e (fun _ _ ↦ rfl)
      (AdicDerivationFiltration.completion (KaehlerDifferential.D R B) J))) a
  exact hd

end FLT.Mazur.AdicCotangentHomMap
