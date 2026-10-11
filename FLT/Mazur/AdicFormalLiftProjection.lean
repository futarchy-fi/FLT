/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormalLiftContinuity
public import FLT.Mazur.AdicFilteredHomExt

/-!
# Completed lifts commute with their actual projections

Agreement over the formal comparison on original elements extends to all
completed elements. The proof uses actual maximal ideals and finite-order
approximation, rather than algebraic generation of completed rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicFormalLiftProjection

open AdicExtensionProjection AdicFormalLiftContinuity

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

/-- The completed lift lies over the given formal equivalence on every completed element. -/
theorem projection_extend (x : AdicCompletion (ideal P I) P.Ring) :
    projection Q J (extend P Q I J e f hf x) = e (projection P I x) := by
  let _ : IsNoetherianRing A := isNoetherianRing_of_surjective P.Ring A
    (algebraMap P.Ring A) P.algebraMap_surjective
  let _ : IsNoetherianRing B := isNoetherianRing_of_surjective Q.Ring B
    (algebraMap Q.Ring B) Q.algebraMap_surjective
  let g := (projection Q J).comp (extend P Q I J e f hf)
  let k := e.toAlgHom.comp (projection P I)
  have ho (a : P.Ring) :
      g (AdicCompletion.of (ideal P I) P.Ring a) =
        k (AdicCompletion.of (ideal P I) P.Ring a) := by
    change projection Q J (extend P Q I J e f hf
      (AdicCompletion.of (ideal P I) P.Ring a)) =
        e (projection P I (AdicCompletion.of (ideal P I) P.Ring a))
    rw [extend_of, projection_of]
    exact hf a
  have hk : ((ideal P I).map
      (algebraMap P.Ring (AdicCompletion (ideal P I) P.Ring))).map k.toRingHom ≤
        J.map (algebraMap B (AdicCompletion J B)) := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro a ha
    change e (projection P I (AdicCompletion.of (ideal P I) P.Ring a)) ∈
      J.map (algebraMap B (AdicCompletion J B))
    rw [projection_of]
    exact AdicMaximalCompletion.map_ideal_le I I.fg_of_isNoetherianRing
      J J.fg_of_isNoetherianRing e
      (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))
  have hg : ((ideal P I).map
      (algebraMap P.Ring (AdicCompletion (ideal P I) P.Ring))).map g.toRingHom ≤
        J.map (algebraMap B (AdicCompletion J B)) := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (AdicCompletion.of (ideal P I) P.Ring a) ∈
      J.map (algebraMap B (AdicCompletion J B))
    rw [ho]
    exact hk (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))
  have he := AdicFilteredHomExt.ext_of (ideal P I) J g hg
    (ideal P I).fg_of_isNoetherianRing k hk ho
  exact AlgHom.congr_fun he x

end FLT.Mazur.AdicFormalLiftProjection
