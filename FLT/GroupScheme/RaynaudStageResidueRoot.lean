/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudStageFamily

/-!
# Roots of residue polynomials at larger embedded stages

Lift a monic separable residue polynomial, choose a root in the fixed closure,
and adjoin that root. Reduction gives a root along the actual stage inclusion.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace RaynaudParameters

variable {R Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [FaithfulSMul R Ω]
  {π : R}

omit [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R Ω] in
/-- A separable residue polynomial acquires a root in a larger embedded stage,
using the residue map of the actual inclusion. -/
theorem exists_larger_stage_residue_root (S : UnramifiedStage (Ω := Ω) π)
    (p : (ResidueField S.1)[X]) (hm : p.Monic) (hs : p.Separable) (hd : p.degree ≠ 0) :
    ∃ T : UnramifiedStage (Ω := Ω) π, ∃ hST : S.1 ≤ T.1, ∃ y : T.1,
      p.eval₂ (ResidueField.map (Subalgebra.inclusion hST).toRingHom)
        (residue T.1 y) = 0 := by
  obtain ⟨P, hPm, hP, hPdeg⟩ := exists_monic_map_residue_eq hm
  have hPd : P.degree ≠ 0 := by rwa [← hPm.degree_map (residue S.1), hP]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero Ω P hPd
  obtain ⟨hD, hF, hL, hU, hπU⟩ :=
    adjoin_prescribed_root_unramified S.uniformizer hPm (hP ▸ hs) x hx
  let B := Algebra.adjoin S.1 {x}
  let hFR : Module.Finite R B := Module.Finite.trans S.1 B
  let hUR : Algebra.FormallyUnramified R B := Algebra.FormallyUnramified.comp R S.1 B
  let T : UnramifiedStage (Ω := Ω) π := ⟨B.restrictScalars R, hD, hFR, hUR, hπU⟩
  have hST : S.1 ≤ T.1 := fun s hs ↦ B.algebraMap_mem ⟨s, hs⟩
  let y : B := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  have hy : aeval y P = 0 := by
    apply Subtype.val_injective
    exact (aeval_algHom_apply B.val y P).symm.trans hx
  refine ⟨T, hST, y, ?_⟩
  change aeval (residue B y) p = 0
  rw [← hP, ← map_aeval_eq_aeval_map (ψ := residue B) (φ := residue S.1) rfl, hy, map_zero]

end RaynaudParameters
