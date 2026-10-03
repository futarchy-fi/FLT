/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRootStage
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.FinitePresentation

/-!
# Common stages in one fixed closure

Two embedded finite unramified DVRs over a Henselian DVR lie in a common
embedded finite unramified DVR with the same base uniformizer.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace RaynaudParameters

variable {R Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field Ω] [Algebra R Ω] [FaithfulSMul R Ω]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Elaborating the restricted scalar tower and its subalgebra inclusions needs this budget.
/-- Construct a common embedded stage; the two inclusions are literal subalgebra
inclusions in the originally specified closure. -/
theorem exists_common_unramified_stage (S T : Subalgebra R Ω)
    [IsDiscreteValuationRing S] [IsDiscreteValuationRing T]
    [Module.Finite R S] [Module.Finite R T]
    [Algebra.FormallyUnramified R S] [Algebra.FormallyUnramified R T]
    {π : R} (hπS : Irreducible (algebraMap R S π)) :
    ∃ (U : Subalgebra R Ω) (_ : IsDiscreteValuationRing U) (_ : Module.Finite R U)
      (_ : Algebra.FormallyUnramified R U), S ≤ U ∧ T ≤ U ∧
        Irreducible (algebraMap R U π) := by
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective R Ω (congrArg Subtype.val h))
  let : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective R Ω (congrArg Subtype.val h))
  let : HenselianLocalRing S := HenselianLocalRing.of_finite (R := R)
  let : Module.Free R T := inferInstance
  let : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale R T := Algebra.Etale.of_formallyUnramified_of_flat
  obtain ⟨y, hy⟩ := IsLocalRing.exists_adjoin_eq_top (R := R) (S := T)
  let P := minpoly R y
  have hm : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have hs : (P.map (residue R)).Separable := by
    rw [IsLocalRing.minpoly_map_residue hy]
    exact Algebra.IsSeparable.isSeparable _ _
  have hSm : (P.map (algebraMap R S)).Monic := hm.map _
  have hSs : ((P.map (algebraMap R S)).map (residue S)).Separable := by
    have heq : (residue S).comp (algebraMap R S) =
        (algebraMap (ResidueField R) (ResidueField S)).comp (residue R) := rfl
    rw [Polynomial.map_map, heq, ← Polynomial.map_map]
    exact hs.map
  have hx : aeval (y : Ω) (P.map (algebraMap R S)) = 0 := by
    rw [aeval_map_algebraMap]
    exact (aeval_algHom_apply T.val y P).trans (by simp [P])
  obtain ⟨hD, hF, hL, hU, hπU⟩ :=
    adjoin_prescribed_root_unramified hπS hSm hSs (y : Ω) hx
  let B := Algebra.adjoin S {(y : Ω)}
  let hFR : Module.Finite R B := Module.Finite.trans S B
  let hUR : Algebra.FormallyUnramified R B := Algebra.FormallyUnramified.comp R S B
  refine ⟨B.restrictScalars R, hD, hFR, hUR, ?_, ?_, ?_⟩
  · intro s hs
    exact (Algebra.adjoin S {(y : Ω)}).algebraMap_mem ⟨s, hs⟩
  · have hgen : Algebra.adjoin R {(y : Ω)} = T := by
      have h := congrArg (Subalgebra.map T.val) hy
      simpa only [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top,
        Subalgebra.range_val, Subalgebra.coe_val] using h
    rw [← hgen]
    apply Algebra.adjoin_le
    intro z hz
    exact Algebra.subset_adjoin hz
  · exact hπU

end RaynaudParameters
