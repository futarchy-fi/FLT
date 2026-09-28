/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.UnramifiedCharacter
public import FLT.GaloisRepresentation.HardlyRamified.CategoryD

/-!
# Pure finite point actions

Purity means equality of the full action with a scalar action on every point.
An everywhere-unramified finite continuous rational Galois module is pure of
character one. This applies to arbitrary finite abelian point groups, including
groups not killed by three; no choice of a constituent is involved.
-/

@[expose] public section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- The action on every point is multiplication by the specified scalar character.
The scalar type is explicit in the character, so it may be `ℤ`, `ℤ_[3]`, or a
coefficient ring acting on the points. -/
def Pure {G R : Type*} (W : Type*) [SMul G W] [SMul R W] (χ : G → R) : Prop :=
  ∀ (g : G) (w : W), g • w = χ g • w

/-- Purity for the integer-valued character one is precisely triviality of the action. -/
theorem pure_one_iff {G W : Type*} [AddGroup W] [SMul G W] :
    Pure W (1 : G → ℤ) ↔ ∀ (g : G) (w : W), g • w = w := by
  simp [Pure]

namespace FiniteContinuousGaloisModule

/-- A finite rational point action unramified at every finite prime cuts out only `ℚ`. -/
theorem pointField_eq_bot_of_everywhere_unramified (W : FiniteContinuousGaloisModule)
    (hW : UnramifiedOutside ∅ W) : W.pointField = ⊥ := by
  apply NumberField.InertiaComparison.intermediateField_eq_bot_of_localInertia
  intro q hq σ hσ
  have hker : Field.absoluteGaloisGroup.map
      (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) σ ∈
      W.pointActionKernel := by
    apply (W.mem_pointActionKernel _).mpr
    let f : ℚ →+* hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ :=
      @algebraMap ℚ _ _ _ DivisionRing.toRatAlgebra
    rw [Subsingleton.elim (algebraMap ℚ
      (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) f]
    exact hW.inertia_trivial q hq (by simp) σ hσ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (AlgEquiv.restrictNormalHom_apply W.pointField
    (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) σ) x).trans
    (x.2 ⟨_, hker⟩)

/-- Everywhere-unramified finite rational point actions are pointwise trivial. -/
theorem pure_one_of_everywhere_unramified (W : FiniteContinuousGaloisModule)
    (hW : UnramifiedOutside ∅ W) :
    Pure W (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ) := by
  apply pure_one_iff.mpr
  have htop : W.pointActionKernel = ⊤ := by
    rw [← W.pointField_fixingSubgroup, W.pointField_eq_bot_of_everywhere_unramified hW,
      IntermediateField.fixingSubgroup_bot]
  intro σ w
  exact (W.mem_pointActionKernel σ).mp (htop ▸ Subgroup.mem_top σ) w

end FiniteContinuousGaloisModule

end ThreeAdicPlan
