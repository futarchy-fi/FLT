/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTwist
public import FLT.GroupScheme.RootModuleLinear

/-!
# Root coefficients of the actual ordinary extension class

When the ratio of the two characters is cyclotomic, evaluation at one and
primitive-root coordinates turn the extracted Hom cocycle into a root cocycle.
The normalized vector difference and simultaneous twists are computed from
the original filtration. No equality of extension classes is an input.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions
open KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
  (α β : Gal(L/K) →* (ZMod p)ˣ)

/-- Evaluation at one followed by the actual root-of-unity coordinate map. -/
def ordinaryRootCoefficients : OrdinaryHomModule α β ≃+ RootModule L p :=
  (ordinaryHomCoordinates α β (primeCyclotomicCharacter (K := K) hζ)).toAddEquiv.trans
    (primeCyclotomicCoordinates (K := K) hζ)

/-- The coefficient map reads the value at one as an exponent of the primitive root. -/
theorem ordinaryRootCoefficients_unit (f : OrdinaryHomModule α β) :
    rootUnit (ordinaryRootCoefficients hζ α β f) =
      ζ ^ ((show ZMod p →ₗ[ZMod p] ZMod p from f) 1).val :=
  rootUnit_primeRootCoordinates hζ ((show ZMod p →ₗ[ZMod p] ZMod p from f) 1)

variable (hχ : homCharacter α β = primeCyclotomicCharacter (K := K) hζ)

include hχ in
/-- The root coefficient map intertwines the given Hom action and field action. -/
theorem ordinaryRootCoefficients_equivariant (g : Gal(L/K)) (f : OrdinaryHomModule α β) :
    ordinaryRootCoefficients hζ α β (g • f) = g • ordinaryRootCoefficients hζ α β f := by
  change primeCyclotomicCoordinates (K := K) hζ
    (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ) (g • f)) = _
  rw [ordinaryHomCoordinates_equivariant α β (primeCyclotomicCharacter hζ) (by simpa using hχ)]
  exact primeCyclotomicCoordinates_equivariant hζ g _

variable [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation (ZMod p) Gal(L/K) V}
  (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : Gal(L/K) ↦ ρ g x))

/-- The root cocycle is constructed from the actual ordinary section. -/
def OrdinaryFiltration.rootCocycle (w : V) (hw : E.projection w = 1) :
    ContinuousCocycle Gal(L/K) (RootModule L p) :=
  mapCoefficientCocycle (ordinaryRootCoefficients hζ α β)
    (ordinaryRootCoefficients_equivariant hζ α β hχ) (E.cocycleOf hρ w hw)

/-- Inverting root coordinates recovers the original normalized vector difference. -/
theorem OrdinaryFiltration.rootCocycle_difference (w : V) (hw : E.projection w = 1)
    (g : Gal(L/K)) :
    E.injection ((primeCyclotomicCoordinates (K := K) hζ).symm
      ((E.rootCocycle hζ α β hχ hρ w hw).val g)) = (β g : ZMod p)⁻¹ • ρ g w - w := by
  change E.injection ((primeCyclotomicCoordinates (K := K) hζ).symm
    (primeCyclotomicCoordinates (K := K) hζ _)) = _
  rw [AddEquiv.symm_apply_apply]
  exact E.cocycleOf_spec hρ w hw g

/-- Each section computes the transported original continuous extension class. -/
theorem OrdinaryFiltration.rootCocycle_class (w : V) (hw : E.projection w = 1) :
    continuousClassMk (E.rootCocycle hζ α β hχ hρ w hw) =
      mapCoefficientClass (ordinaryRootCoefficients hζ α β)
        (ordinaryRootCoefficients_equivariant hζ α β hχ) (E.extensionClass hρ) := by
  rw [E.extensionClass_eq hρ w hw]
  rfl

/-- A simultaneous twist leaves the actual root-valued cocycle unchanged. -/
theorem OrdinaryFiltration.rootCocycle_twist (ψ : Gal(L/K) →* (ZMod p)ˣ)
    (hψ : Continuous (fun g : Gal(L/K) ↦ (ψ g : ZMod p)))
    (w : V) (hw : E.projection w = 1) :
    (E.twist ψ).rootCocycle hζ (α * ψ) (β * ψ)
      (by rw [homCharacter_twist, hχ]) (OrdinaryFiltration.continuous_twistOrbit ψ hρ hψ) w hw =
      E.rootCocycle hζ α β hχ hρ w hw := by
  unfold OrdinaryFiltration.rootCocycle
  rw [E.cocycleOf_twist ψ hρ hψ]
  rfl

end GaloisRepresentation.Extensions
