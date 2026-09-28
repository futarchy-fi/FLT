/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.KummerModThreeCyclotomic
public import FLT.GroupScheme.CartierDualModelIso
public import FLT.GroupScheme.OrderThreeModelIdentification

/-!
# Integral identification of the cyclotomic order-three model

For a point module killed by three, the mod-three cyclotomic action makes its
full geometric character dual trivial. The integral Cartier dual has precisely
these characters as points. Its one-dimensional trivial module therefore
identifies it with `constantThree`; integral biduality then identifies the
original model with `muThree`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The character group of a finite abelian group is abstractly additively isomorphic
to that group. This choice does not assert Galois equivariance. -/
def FiniteContinuousGaloisModule.characterDualUnderlyingEquiv
    (W : FiniteContinuousGaloisModule) : W.characterDual ≃+ W :=
  (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
    (Multiplicative W) (AlgebraicClosure ℚ)).some.toAdditive

/-- A cyclotomic mod-three point action makes the full character dual trivial. -/
theorem characterDual_trivial_of_modThreeCyclotomic
    (H : FiniteFlatObject ZInvTwo) [Module (ZMod 3) H.points]
    (hcycl : ∀ (σ : Γ) (x : H.points),
      σ • x = (modThreeCyclotomic σ : ZMod 3) • x)
    (σ : Γ) (φ : H.points.characterDual) : σ • φ = φ := by
  let ψ : H.points.Characters := φ
  have h (w : H.points) :
      σ • ψ (Multiplicative.ofAdd w) = ψ (Multiplicative.ofAdd (σ • w)) := by
    have hw : (ψ (Multiplicative.ofAdd w) : AlgebraicClosure ℚ) ^ 3 = 1 := by
      have hk : (3 : ℕ) • w = 0 := points_killedBy_three H w
      have hpow : ψ (Multiplicative.ofAdd w) ^ 3 = 1 := by
        rw [← map_pow, ← ofAdd_nsmul, hk, ofAdd_zero, map_one]
      exact congrArg Units.val hpow
    have hs : (modThreeCyclotomic σ : ZMod 3) • w =
        (modThreeCyclotomic σ : ZMod 3).val • w := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
    rw [hcycl, hs, ofAdd_nsmul, map_pow]
    apply Units.ext
    exact modThreeCyclotomic_spec σ _ hw
  change H.points.conjugateCharacter σ ψ = ψ
  apply MonoidHom.ext
  intro w
  change σ • ψ (Multiplicative.ofAdd (σ⁻¹ • w.toAdd)) = ψ w
  simpa only [smul_inv_smul, ofAdd_toAdd] using h (σ⁻¹ • w.toAdd)

/-- One-dimensional cyclotomic mod-three points determine the integral cube-root model. -/
theorem exists_iso_muThree (H : FiniteFlatObject ZInvTwo)
    [Module (ZMod 3) H.points] (hdim : Module.finrank (ZMod 3) H.points = 1)
    (hcycl : ∀ (σ : Γ) (x : H.points),
      σ • x = (modThreeCyclotomic σ : ZMod 3) • x) :
    Nonempty (H.Iso muThree) := by
  let e : H.cartierDual.points ≃+ H.points :=
    H.cartierDualPointEquiv.trans H.points.characterDualUnderlyingEquiv
  have hkill : ∀ x : H.cartierDual.points, (3 : ℕ) • x = 0 := by
    intro x
    apply e.injective
    rw [map_nsmul, map_zero]
    exact points_killedBy_three H (e x)
  let : Module (ZMod 3) H.cartierDual.points := AddCommGroup.zmodModule hkill
  let eL : H.cartierDual.points ≃ₗ[ZMod 3] H.points :=
    { e with map_smul' := ZMod.map_smul e }
  have hdimDual : Module.finrank (ZMod 3) H.cartierDual.points = 1 :=
    eL.finrank_eq.trans hdim
  have htriv : ∀ (σ : Γ) (x : H.cartierDual.points), σ • x = x := by
    intro σ x
    apply H.cartierDualPointEquiv.injective
    rw [H.cartierDualPointEquiv_smul, characterDual_trivial_of_modThreeCyclotomic H hcycl]
  obtain ⟨i, _⟩ := exists_iso_constantThree H.cartierDual hdimDual htriv
  exact ⟨isoMuThreeOfDualConstant H i⟩

end ThreeAdicPlan
