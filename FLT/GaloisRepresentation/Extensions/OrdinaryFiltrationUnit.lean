/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTwist
public import FLT.GaloisRepresentation.Extensions.OrdinaryTwist

/-!
# Unit membership for actual ordinary filtrations

The proved basis and twist formulas for extracted extension classes specialize
the independent unit-subspace invariance to actual middle representations.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions.OrdinaryFiltration

open KummerTheory

variable {K L k V : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime] [Field k] [Algebra (ZMod p) k]
    [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [TopologicalSpace V] [DiscreteTopology V]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ p = Units.map (algebraMap K L) q)
    (A : ValuationSubring K)
    {ρ : Representation k Gal(L/K) V} {α β : Gal(L/K) →* kˣ}
    (hχ : homCharacter α β = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
      (primeCyclotomicCharacter (K := K) hζ))
    (E : OrdinaryFiltration ρ α β)
    (hρ : ∀ x : V, Continuous (fun g : Gal(L/K) ↦ ρ g x))

/-- The independent unit condition is invariant under changing both actual line bases. -/
theorem extensionUnit_change_bases (D : OrdinaryFiltration ρ α β) (a b : kˣ)
    (hi : D.injection = (a : k) • E.injection)
    (hp : D.projection = (b : k)⁻¹ • E.projection) :
    OrdinaryUnitClass hζ roots A (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ) (D.extensionClass hρ) ↔
    OrdinaryUnitClass hζ roots A (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ) (E.extensionClass hρ) := by
  rw [E.extensionClass_change_bases D hρ a b hi hp]
  exact ordinaryHomUnit_basis_iff hζ roots A α β hχ a b (E.extensionClass hρ)

/-- The independent unit condition is invariant under twisting the actual representation. -/
theorem extensionUnit_twist (ψ : Gal(L/K) →* kˣ)
    (hψ : Continuous (fun g : Gal(L/K) ↦ (ψ g : k))) :
    OrdinaryUnitClass hζ roots A
      (ordinaryHomCoordinates (α * ψ) (β * ψ) (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_twist_equivariant α β _ hχ ψ)
      ((E.twist ψ).extensionClass (continuous_twistOrbit ψ hρ hψ)) ↔
    OrdinaryUnitClass hζ roots A (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ))
      (ordinaryHomCoordinates_equivariant α β _ hχ) (E.extensionClass hρ) := by
  rw [E.extensionClass_twist ψ hρ hψ]
  exact ordinaryHomUnit_twist_iff hζ roots A α β hχ ψ (E.extensionClass hρ)

end GaloisRepresentation.Extensions.OrdinaryFiltration
