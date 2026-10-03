/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaDescentUniformizer
public import FLT.GroupScheme.RaynaudStageHenselian
public import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Henselianity of the actual inertia descent base

The rational completion integers inherit adic completeness from the p-adic
integers. The finite unramified integral closure used by inertia descent is
then Henselian, with no assumed Henselian structure on the extension.
-/

@[expose] public noncomputable section

open NumberField IsLocalRing

/-- Completeness at the rational place is transported from the p-adic integers. -/
theorem rationalCompletionIntegers_adicComplete (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (maximalIdeal ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ))
      ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) := by
  let e : ℤ_[p] ≃+* (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ :=
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  have he : (maximalIdeal ℤ_[p]).map e.toRingHom =
      maximalIdeal ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) := by
    have hpR : Irreducible (e (p : ℤ_[p])) :=
      (MulEquiv.irreducible_iff (f := e)).mpr PadicInt.irreducible_p
    rw [PadicInt.irreducible_p.maximalIdeal_eq, hpR.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
    rfl
  rw [← he]
  exact (IsAdicComplete.congr_ringEquiv (maximalIdeal ℤ_[p]) e).mpr inferInstance

variable {F X : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) [AddCommGroup X]
    [DistribMulAction (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)) X]
    [Finite X] [ContinuousSMulDiscrete (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)) X]

local notation "L₀" => InertiaDescent.field (X := X) (localInertiaGroup v)
local notation "R₀" => v.adicCompletionIntegers F
local notation "S₀" => IntegralClosure R₀ L₀

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual unramified descent ring over a complete base is Henselian. -/
theorem inertiaDescentIntegers_henselian [IsAdicComplete (maximalIdeal R₀) R₀] :
    HenselianLocalRing S₀ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
  have hπS := inertiaDescentIntegers_irreducible (X := X) v hπ
  let : Module.Finite R₀ S₀ := IsIntegralClosure.finite R₀ (v.adicCompletion F) L₀ S₀
  apply RaynaudParameters.unramified_stage_henselian (R := R₀)
  rw [hπ.maximalIdeal_eq, hπS.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
