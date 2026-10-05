/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.SerreWeight.CoefficientOrdinaryInput

/-!
# Independence of the extracted ordinary input under bases and twists

The complete normalized input, hence its finite recipe table, is invariant
under rescaling the two lines and simultaneous character twists. This does
not compare different invariant lines or identify the numerical Serre weight.
-/

@[expose] public noncomputable section
namespace SerreWeightRecipe

/-- The two data fields determine the normalized input; the other fields are proofs. -/
theorem ReducibleInput.ext_data {p : ℕ} {d e : ReducibleInput p}
    (hb : d.exponent = e.exponent) (hc : d.extensionCase = e.extensionCase) : d = e := by
  cases d
  cases e
  cases hb
  cases hc
  rfl

end SerreWeightRecipe

namespace GaloisRepresentation.Extensions.OrdinaryFiltration
open SerreWeight SerreWeightRecipe
variable {G k V : Type*} [Group G] [Field k] {p : ℕ} [Fact p.Prime]
  [AddCommGroup V] [Module k V]
  [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k G V} {α β : G →* kˣ}
  (E : OrdinaryFiltration ρ α β) (hρ : ∀ x : V, Continuous (fun g ↦ ρ g x))
  (f : ZMod p →+* k) (I : Subgroup G) (ε : G →* (ZMod p)ˣ)
  (hε : Function.Surjective (ε.comp I.subtype))
  (hker : (ε.comp I.subtype).ker ≤ ((homCharacter α β).comp I.subtype).ker)

/-- Rescaling both line coordinates preserves all data of the extracted input. -/
theorem coefficientOrdinaryInput_change_bases (D : OrdinaryFiltration ρ α β) (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (hp : D.projection = (b : k)⁻¹ • E.projection) :
    D.coefficientOrdinaryInput hρ f I ε hε hker =
      E.coefficientOrdinaryInput hρ f I ε hε hker :=
  ReducibleInput.ext_data rfl (E.ordinaryBranch_change_bases hρ I _ D a b hi hp)

/-- Simultaneous twists preserve the normalized exponent and the whole-local branch. -/
theorem coefficientOrdinaryInput_twist (ψ : G →* kˣ)
    (hψ : Continuous (fun g : G ↦ (ψ g : k)))
    (hk : (ε.comp I.subtype).ker ≤
      ((homCharacter (α * ψ) (β * ψ)).comp I.subtype).ker) :
    (E.twist ψ).coefficientOrdinaryInput (continuous_twistOrbit ψ hρ hψ) f I ε hε hk =
      E.coefficientOrdinaryInput hρ f I ε hε hker := by
  apply ReducibleInput.ext_data
  · change coefficientCharacterExponent f _ _ hε hk = _
    simp only [homCharacter_twist]
    rfl
  · exact E.ordinaryBranch_twist hρ I _ ψ hψ

/-- The finite recipe table is consequently independent of the chosen two bases. -/
theorem coefficientOrdinaryRecipe_change_bases (D : OrdinaryFiltration ρ α β) (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (hp : D.projection = (b : k)⁻¹ • E.projection) :
    reducible p (D.coefficientOrdinaryInput hρ f I ε hε hker) =
      reducible p (E.coefficientOrdinaryInput hρ f I ε hε hker) :=
  congrArg (reducible p) (E.coefficientOrdinaryInput_change_bases hρ f I ε hε hker D a b hi hp)

/-- Simultaneous twists also preserve the normalized finite table. -/
theorem coefficientOrdinaryRecipe_twist (ψ : G →* kˣ)
    (hψ : Continuous (fun g : G ↦ (ψ g : k)))
    (hk : (ε.comp I.subtype).ker ≤
      ((homCharacter (α * ψ) (β * ψ)).comp I.subtype).ker) :
    reducible p ((E.twist ψ).coefficientOrdinaryInput
      (continuous_twistOrbit ψ hρ hψ) f I ε hε hk) =
      reducible p (E.coefficientOrdinaryInput hρ f I ε hε hker) :=
  congrArg (reducible p) (E.coefficientOrdinaryInput_twist hρ f I ε hε hker ψ hψ hk)

end GaloisRepresentation.Extensions.OrdinaryFiltration
