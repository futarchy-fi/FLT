/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineConvolutionPoint
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Approximate convolution roots from truncated points

Projectivity lifts a quotient-valued algebra point to an integral linear
functional. For a model killed by three, this functional has convolution cube
congruent to one to the original precision. Only the analytic correction to
an exact convolution root remains; multiplicativity is recovered separately.
-/

@[expose] public noncomputable section

open WithConv

namespace LinearMap

variable {R A T U : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [Coalgebra R A] [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]

/-- Postcomposition by an algebra map commutes with convolution powers. -/
theorem convPow_postcomp_algHom (q : T →ₐ[R] U)
    (F : WithConv (A →ₗ[R] T)) (n : ℕ) :
    q.toLinearMap.comp (F ^ n).ofConv =
      (toConv (q.toLinearMap.comp F.ofConv) ^ n).ofConv := by
  induction n with
  | zero => ext a; simp
  | succ n ih =>
    rw [pow_succ, algHom_comp_convMul_distrib, ih]
    rfl

end LinearMap

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- Every truncated point of a killed-by-three model lifts to an integral
linear functional whose convolution cube has the original error precision. -/
theorem FF.exists_approximate_conv_cube_root (M : FF ℤ_[3] ℚ_[3])
    (hM : KilledBy 3 M) (m : ℚ)
    (u : M.CoordinateRing →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) :
    ∃ F : WithConv (M.CoordinateRing →ₗ[ℤ_[3]] ThreeAdicIntegers E),
      (∀ a, Ideal.Quotient.mk (threeAdicValuationIdeal E m) (F a) = u a) ∧
      ∀ a, (F ^ 3 - 1).ofConv a ∈ threeAdicValuationIdeal E m := by
  let freeCoordinateRing : Module.Free ℤ_[3] M.CoordinateRing :=
    Module.free_of_flat_of_isLocalRing
  let q := Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E m)
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap u.toLinearMap
    (Ideal.Quotient.mk_surjective)
  refine ⟨toConv f, fun a ↦ LinearMap.congr_fun hf a, fun a ↦ ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hu : toConv u.toLinearMap ^ 3 = 1 := by
    rw [← AlgHom.toLinearMap_convPow,
      HopfAlgebra.convPow_eq_one_of_id 3 (M.id_convPow_eq_one 3 hM),
      AlgHom.toLinearMap_convOne]
  have he := LinearMap.convPow_postcomp_algHom q (toConv f) 3
  rw [show (toConv f).ofConv = f from rfl, hf, hu] at he
  have ha := LinearMap.congr_fun he a
  change q ((toConv f ^ 3).ofConv a - (1 : WithConv (M.CoordinateRing →ₗ[ℤ_[3]]
    ThreeAdicIntegers E)).ofConv a) = 0
  rw [map_sub]
  change q.toLinearMap ((toConv f ^ 3).ofConv a) - _ = 0
  simp only [LinearMap.comp_apply] at ha
  rw [ha]
  simp [q]

/-- Correcting an integral linear lift by precision `m - 1` gives the
compatibility needed to recover an algebra point at Fontaine precision. -/
theorem FF.exists_compatible_point_of_conv_correction (M : FF ℤ_[3] ℚ_[3])
    {m : ℚ} (hm : 3 / 2 < m)
    (u : M.CoordinateRing →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m)
    (F G : WithConv (M.CoordinateRing →ₗ[ℤ_[3]] ThreeAdicIntegers E))
    (hF : ∀ a, Ideal.Quotient.mk (threeAdicValuationIdeal E m) (F a) = u a)
    (hG : G ^ 3 = 1)
    (hclose : ∀ a, (G - F).ofConv a ∈ threeAdicValuationIdeal E (m - 1)) :
    ∃ v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
        (Ideal.Quotient.factorₐ ℤ_[3]
          (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp u := by
  let cocommCoordinateRing := M.coordinateRing_cocomm
  let q := Ideal.Quotient.factorₐ ℤ_[3]
    (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))
  obtain ⟨v, _, hv⟩ := exists_algHom_of_conv_cube_root E (by linarith) G hG (q.comp u) (by
    intro a
    have hc := Ideal.Quotient.eq.mpr (hclose a)
    change Ideal.Quotient.mk _ (G a) = Ideal.Quotient.mk _ (F a) at hc
    rw [hc]
    have hh := congrArg q (hF a)
    exact hh)
  exact ⟨v, hv⟩

end ThreeAdicPlan
