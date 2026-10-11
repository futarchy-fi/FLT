/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentTransportDerivative

/-!
# Equivalence of completed original cotangent modules

A formal equivalence preserving the original ideal filtrations induces
a semilinear equivalence of the completed original differential modules.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCotangentTransportMap

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsNoetherianRing A] [IsNoetherianRing B]
  [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]]
  (I : Ideal A) (J : Ideal B) (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)
  (he : (I.map (algebraMap A (AdicCompletion I A))).map e.toRingHom =
    J.map (algebraMap B (AdicCompletion J B)))

omit [IsNoetherianRing A] [IsNoetherianRing B]
  [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]] in
/-- The two underlying ring maps are inverse in the semilinear-map API. -/
theorem inversePair : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  ⟨RingHom.ext e.symm_apply_apply, RingHom.ext e.apply_symm_apply⟩

omit [IsNoetherianRing A] [IsNoetherianRing B]
  [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]] in
/-- The inverse pair also works in the reverse direction. -/
theorem inversePairSymm : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  ⟨RingHom.ext e.apply_symm_apply, RingHom.ext e.symm_apply_apply⟩

attribute [local instance] inversePair inversePairSymm

include he

omit [IsNoetherianRing A] [IsNoetherianRing B]
  [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]] in
/-- Equality of extended original ideals also holds for the inverse formal equivalence. -/
theorem inverse_ideal :
    (J.map (algebraMap B (AdicCompletion J B))).map e.symm.toRingHom =
      I.map (algebraMap A (AdicCompletion I A)) := by
  rw [← he, Ideal.map_map]
  have hc : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
    ext a : 1
    exact e.symm_apply_apply a
  rw [hc, Ideal.map_id]

/-- Applying the forward and inverse cotangent maps recovers every completed differential. -/
theorem map_symm_map (x : AdicCompletion I Ω[A⁄R]) :
    map J I e.symm (map I J e x) = x := by
  have hc : (map J I e.symm).comp (map I J e) =
      LinearMap.id (R := AdicCompletion I A) (M := AdicCompletion I Ω[A⁄R]) := by
    apply AdicFiniteModuleExt.ext_differentials I
    intro a
    change map J I e.symm (map I J e
      (AdicCompletion.of I Ω[A⁄R] (KaehlerDifferential.D R A a))) = _
    rw [map_of_D, map_completed J I e.symm (inverse_ideal I J e he),
      e.symm_apply_apply, AdicDerivationFiltration.completion_of]
    rfl
  exact LinearMap.congr_fun hc x

/-- Applying the inverse and forward cotangent maps recovers every target differential. -/
theorem map_map_symm (x : AdicCompletion J Ω[B⁄R]) :
    map I J e (map J I e.symm x) = x :=
  map_symm_map J I e.symm (inverse_ideal I J e he) x

/-- A filtration-preserving formal equivalence identifies completed original differentials. -/
def equiv : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
    (AdicCompletion I Ω[A⁄R]) (AdicCompletion J Ω[B⁄R]) :=
  { map I J e with
    invFun := map J I e.symm
    left_inv := map_symm_map I J e he
    right_inv := map_map_symm I J e he }

/-- The equivalence has exactly the previously constructed forward cotangent map. -/
@[simp] theorem equiv_apply (x : AdicCompletion I Ω[A⁄R]) :
    equiv I J e he x = map I J e x := rfl

/-- The inverse equivalence is the cotangent map of the inverse formal equivalence. -/
@[simp] theorem equiv_symm_apply (x : AdicCompletion J Ω[B⁄R]) :
    (equiv I J e he).symm x = map J I e.symm x := rfl

end FLT.Mazur.AdicCotangentTransportMap
