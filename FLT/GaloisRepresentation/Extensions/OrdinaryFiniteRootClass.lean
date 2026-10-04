/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTwist
public import FLT.GroupScheme.FiniteRootProjection

/-!
# Prime-linear projections of the original ordinary class

The class is extracted from the given filtration and projected by arbitrary
prime-linear functionals on the residual field. Changing the section preserves
these classes by construction.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions
open KummerTheory

variable {K L k V : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [Field k] [Algebra (ZMod p) k]
  {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (α β : Gal(L/K) →* kˣ)
  (hχ : homCharacter α β = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
    (primeCyclotomicCharacter (K := K) hζ))
  [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k Gal(L/K) V} (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : Gal(L/K) ↦ ρ g x))

/-- Evaluation at one transports the original Hom cocycle into its cyclotomic line. -/
def OrdinaryFiltration.finiteCyclotomicCocycle (w : V) (hw : E.projection w = 1) :
    ContinuousCocycle Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k) :=
  mapCoefficientCocycle
    (ordinaryHomCoordinates α β (primeCyclotomicCharacter (K := K) hζ)).toAddEquiv
    (ordinaryHomCoordinates_equivariant α β _ hχ) (E.cocycleOf hρ w hw)

/-- The transported representative computes the original extension class. -/
theorem OrdinaryFiltration.finiteCyclotomicCocycle_class (w : V) (hw : E.projection w = 1) :
    continuousClassMk (E.finiteCyclotomicCocycle hζ α β hχ hρ w hw) =
      mapCoefficientClass
        (ordinaryHomCoordinates α β (primeCyclotomicCharacter (K := K) hζ)).toAddEquiv
        (ordinaryHomCoordinates_equivariant α β _ hχ) (E.extensionClass hρ) := by
  rw [E.extensionClass_eq hρ w hw]
  rfl

/-- The root cocycle attached to a prime-linear functional uses that same section. -/
def OrdinaryFiltration.finiteRootCocycle (a : Module.Dual (ZMod p) k)
    (w : V) (hw : E.projection w = 1) : ContinuousCocycle Gal(L/K) (RootModule L p) :=
  KummerTheory.finiteRootCocycle hζ a (E.finiteCyclotomicCocycle hζ α β hχ hρ w hw)

/-- Every section computes the same projected original extension class. -/
theorem OrdinaryFiltration.finiteRootCocycle_class (a : Module.Dual (ZMod p) k)
    (w : V) (hw : E.projection w = 1) :
    continuousClassMk (E.finiteRootCocycle hζ α β hχ hρ a w hw) =
      finiteRootClass hζ a
        (mapCoefficientClass
        (ordinaryHomCoordinates α β (primeCyclotomicCharacter (K := K) hζ)).toAddEquiv
          (ordinaryHomCoordinates_equivariant α β _ hχ) (E.extensionClass hρ)) := by
  rw [← E.finiteCyclotomicCocycle_class hζ α β hχ hρ w hw, finiteRootClass_mk]
  rfl

end GaloisRepresentation.Extensions
