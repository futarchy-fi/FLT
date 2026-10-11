/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicMaximalCompletion
public import FLT.Mazur.AdicIdealFilteredMap
public import FLT.Mazur.AdicExtensionProjection

/-!
# Continuity of actual lifts over formal comparisons

A lift over an equivalence of completions at maximal ideals preserves the
presenting-ring filtrations. This follows from the actual surjective
completed projection and the maximal ideals of the completed rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalLiftContinuity

open AdicExtensionProjection AdicMaximalCompletion

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (P : Algebra.Extension.{u} R A) (Q : Algebra.Extension.{u} R B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)
  (f : P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) =
    e (AdicCompletion.of I A (algebraMap P.Ring A x)))

include hf in
/-- A genuine lift over the formal comparison preserves the original presenting ideal. -/
theorem ideal_le : (ideal P I).map f.toRingHom ≤
    (ideal Q J).map (algebraMap Q.Ring (AdicCompletion (ideal Q J) Q.Ring)) := by
  let _ : IsNoetherianRing A := isNoetherianRing_of_surjective P.Ring A
    (algebraMap P.Ring A) P.algebraMap_surjective
  let _ : IsNoetherianRing B := isNoetherianRing_of_surjective Q.Ring B
    (algebraMap Q.Ring B) Q.algebraMap_surjective
  let _ : (ideal Q J).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Q.algebraMap_surjective
  let _ := localRing J J.fg_of_isNoetherianRing
  let _ := localRing (ideal Q J) (ideal Q J).fg_of_isNoetherianRing
  let _ : IsLocalHom (projection Q J).toRingHom :=
    IsLocalHom.of_surjective _ (projection_surjective Q J)
  rw [← maximalIdeal_eq (ideal Q J) (ideal Q J).fg_of_isNoetherianRing,
    ← IsLocalRing.maximalIdeal_comap (projection Q J).toRingHom,
    Ideal.map_le_iff_le_comap]
  intro x hx
  change projection Q J (f x) ∈ IsLocalRing.maximalIdeal (AdicCompletion J B)
  rw [hf, maximalIdeal_eq J J.fg_of_isNoetherianRing]
  exact map_ideal_le I I.fg_of_isNoetherianRing J J.fg_of_isNoetherianRing e
    (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx))

/-- The actual lift extends through the completion of its presenting ring. -/
def extend : AdicCompletion (ideal P I) P.Ring →ₐ[R]
    AdicCompletion (ideal Q J) Q.Ring :=
  AdicIdealFilteredMap.extend (ideal P I) (ideal Q J) f (ideal_le P Q I J e f hf)

/-- The completed lift retains the constructed original lift. -/
@[simp] theorem extend_of (x : P.Ring) :
    extend P Q I J e f hf (AdicCompletion.of (ideal P I) P.Ring x) = f x :=
  AdicIdealFilteredMap.extend_of (ideal P I) (ideal Q J) f (ideal_le P Q I J e f hf) x

end FLT.Mazur.AdicFormalLiftContinuity
