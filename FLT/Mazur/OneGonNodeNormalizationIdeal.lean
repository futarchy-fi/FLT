/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The scheme-theoretic node fiber in the one-gon normalization chart

Extending the original node ideal to its actual polynomial normalization
gives the principal ideal X(X-1). Its quotient has precisely the two reduced
rational branches; the formulas work over every commutative coefficient ring.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.OneGonNodeNormalizationIdeal
open PolygonNodePresentation
variable (R : Type*) [CommRing R]

/-- The original node ideal extends to the product of the two endpoint equations. -/
theorem node_ideal_map :
    (RingHom.ker (bEval (R := R)).toRingHom).map (B (R := R)).val.toRingHom =
      Ideal.span ({X * (X - 1)} : Set R[X]) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change p.val ∈ Ideal.span ({X * (X - 1)} : Set R[X])
    rw [Ideal.mem_span_singleton]
    have hp : bEval p = 0 := hp
    simpa only [hp, map_zero, sub_zero] using conductor_dvd p
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ (show u (R := R) ∈ RingHom.ker (bEval (R := R)).toRingHom by
      simp [RingHom.mem_ker, bEval, u])

/-- Evaluate a polynomial on the two original branches of the pinching chart. -/
def endpoints : R[X] →+* R × R := (evalRingHom 0).prod (evalRingHom 1)

/-- The two branch values can be prescribed independently over the original ring. -/
theorem endpoints_surjective : Function.Surjective (endpoints R) := by
  rintro ⟨a, b⟩
  refine ⟨C a * (1 - X) + C b * X, ?_⟩
  ext <;> simp [endpoints]

/-- The branch evaluation kernel is exactly the original extended node ideal. -/
theorem endpoints_ker :
    RingHom.ker (endpoints R) = Ideal.span ({X * (X - 1)} : Set R[X]) := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hp
    have h0 : p.eval 0 = 0 := congrArg Prod.fst hp
    have h1 : p.eval 1 = 0 := congrArg Prod.snd hp
    have hB : p ∈ B (R := R) := (mem_B p).mpr (h0.trans h1.symm)
    have hv : bEval (⟨p, hB⟩ : B (R := R)) = 0 := h0
    simpa only [hv, map_zero, sub_zero] using conductor_dvd (⟨p, hB⟩ : B (R := R))
  · rintro ⟨q, rfl⟩
    ext <;> simp [endpoints]

/-- The actual normalization fiber ring is the product of its original two residue rings. -/
def nodeFiberEquiv :
    R[X] ⧸ (RingHom.ker (bEval (R := R)).toRingHom).map (B (R := R)).val.toRingHom ≃+*
      R × R :=
  (Ideal.quotEquivOfEq (by rw [node_ideal_map, endpoints_ker])).trans
    (RingHom.quotientKerEquivOfSurjective (endpoints_surjective R))

end FLT.Mazur.OneGonNodeNormalizationIdeal
