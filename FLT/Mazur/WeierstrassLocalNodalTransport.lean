/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalCoefficientExtension
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Nodal invariants on the extended original local equation

Local coefficient maps preserve bad discriminant and invertible c₄. The
original generic coordinate equation supplies ellipticity after extension,
and an additional integral change retains its explicit original coordinates.
-/

@[expose] public noncomputable section
open WeierstrassCurve IsLocalRing
namespace FLT.Mazur.WeierstrassLocalNodalTransport

variable {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  (φ : A →+* B) [IsLocalHom φ] (W : WeierstrassCurve A)

/-- Bad discriminant is preserved and reflected by the exact local coefficient map. -/
theorem discriminant_mem_iff :
    (W.map φ).Δ ∈ maximalIdeal B ↔ W.Δ ∈ maximalIdeal A := by
  rw [map_Δ, ← maximalIdeal_comap φ]
  rfl

omit [IsLocalRing A] [IsLocalRing B] in
/-- The multiplicative invariant stays invertible on the extended original cubic. -/
theorem c₄_isUnit_iff : IsUnit (W.map φ).c₄ ↔ IsUnit W.c₄ := by
  rw [map_c₄, isUnit_map_iff]

variable {R K L : Type} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Algebra A K] [Algebra B L]
  (hφ : (algebraMap B L).comp φ = (algebraMap K L).comp (algebraMap A K))
  (E : WeierstrassCurve R) [E.IsElliptic] (C : VariableChange K)
  (hC : C • E.map (algebraMap R K) = W.map (algebraMap A K))

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom φ] in
include hφ hC in
/-- Generic ellipticity follows from the given original equation, without a new assumption. -/
theorem generic_isElliptic : ((W.map φ).map (algebraMap B L)).IsElliptic := by
  rw [← WeierstrassLocalCoefficientExtension.changeEquation φ hφ E W C hC]
  infer_instance

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom φ] [E.IsElliptic] in
include hφ hC in
/-- An integral normalization composes with the original generic variable change. -/
theorem normalized_changeEquation (T : VariableChange B) :
    (T.map (algebraMap B L) * C.map (algebraMap K L)) • E.map (algebraMap R L) =
      (T • W.map φ).map (algebraMap B L) := by
  rw [mul_smul, WeierstrassLocalCoefficientExtension.changeEquation φ hφ E W C hC,
    map_variableChange]

end FLT.Mazur.WeierstrassLocalNodalTransport
