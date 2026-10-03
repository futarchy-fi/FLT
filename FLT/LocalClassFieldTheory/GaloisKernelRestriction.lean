/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisInflationH2

/-!
# Restriction to the kernel in a Galois tower

This is the actual map of continuous cohomology induced by inclusion of
the restriction kernel, with the unchanged field-unit coefficients.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)))

/-- The restriction kernel is compact for its induced Krull topology. -/
instance galoisRestrictionKernel_compactSpace : CompactSpace N :=
  isCompact_iff_compactSpace.mp
    (isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous E)).isCompact

/-- Identity on coefficients, viewed along inclusion of the restriction kernel. -/
def galoisKernelRestrictionCoefficients :
    Rep.res (N).subtype (Rep.of (Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ N (Additive Lˣ)) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- Restriction to the actual kernel as a morphism on continuous cohomology. -/
def galoisKernelRestriction (n : ℕ) :
    continuousCohomology ℤ Gal(L/K) (Additive Lˣ) n ⟶
      continuousCohomology ℤ N (Additive Lˣ) n :=
  homologyMap (continuousRestriction (N).subtype continuous_subtype_val
    (galoisKernelRestrictionCoefficients K L E)) n

/-- The kernel restriction is represented by restricting the explicit two-cocycle. -/
theorem galoisKernelRestriction_class (c : C(Gal(L/K) × Gal(L/K), Additive Lˣ))
    (hc : IsCocycle₂ c) :
    (galoisKernelRestriction K L E 2).hom (integralH2Class (k := ℤ) c hc) =
      integralH2Class (k := ℤ)
        (continuousInflatedTwoCochain (N).subtype continuous_subtype_val
          (galoisKernelRestrictionCoefficients K L E) c)
        (continuousInflatedTwoCochain_isCocycle (N).subtype continuous_subtype_val
          (galoisKernelRestrictionCoefficients K L E) c hc) :=
  continuousInflationH2_class (N).subtype continuous_subtype_val
    (galoisKernelRestrictionCoefficients K L E) c hc

/-- Vanishing of the kernel restriction gives its actual bounding cochain. -/
theorem galoisKernelRestriction_class_eq_zero (c : C(Gal(L/K) × Gal(L/K), Additive Lˣ))
    (hc : IsCocycle₂ c) :
    (galoisKernelRestriction K L E 2).hom (integralH2Class (k := ℤ) c hc) = 0 ↔
      ∃ b : C(N, Additive Lˣ), ∀ g h : N,
        g • b h - b (g * h) + b g = c (g, h) := by
  rw [galoisKernelRestriction_class, integralH2Class_eq_zero]
  rfl

end LocalClassFieldTheory
