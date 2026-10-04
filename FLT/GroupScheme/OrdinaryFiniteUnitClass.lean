/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryFiniteKummerClass
public import FLT.GroupScheme.FiniteUnitReconstruction

/-!
# Integral unit classes over arbitrary finite residual fields

All prime-linear projections of the original class have parameters constructed
on the original integral fibre. Finite-basis reconstruction puts that class
in the independently defined extended unit subspace.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HopfAlgebra
open NumberField IsLocalRing GaloisRepresentation.Extensions KummerTheory
namespace ThreeAdicPlan

variable {K k : Type} [Field K] [NumberField K] [Field k] [Finite k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) k X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hα : α = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
    (primeCyclotomicCharacter hζ))

local instance : Finite (Module.Dual (ZMod p) k) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

variable (hβ : β = 1)

variable [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous
    (fun g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K) ↦ g • x))

include he in
/-- The original finite-coefficient extension has integral unit Kummer coefficients. -/
theorem ordinaryFiniteExtensionClass_unit :
    IsExtendedUnitClass hζ k (exists_unit_root (L := AlgebraicClosure (v.adicCompletion K)))
      (v.adicCompletionIntegers K)
      (mapCoefficientClass
        (ordinaryHomCoordinates α β (primeCyclotomicCharacter hζ)).toAddEquiv
        (ordinaryHomCoordinates_equivariant α β _ (ordinaryFinite_homCharacter v p hζ hα hβ))
        (E.extensionClass hρ)) := by
  obtain ⟨w, hw⟩ := E.surjective 1
  rw [← E.finiteCyclotomicCocycle_class hζ α β
    (ordinaryFinite_homCharacter v p hζ hα hβ) hρ w hw]
  let c := E.finiteCyclotomicCocycle hζ α β
    (ordinaryFinite_homCharacter v p hζ hα hβ) hρ w hw
  change (linearClassEquiv (k := k)).symm
    (linearClassEquiv (Submodule.Quotient.mk (linearCocycleOf (k := k) c))) ∈ _
  rw [Equiv.symm_apply_apply]
  apply finiteRootProjections_mem_extendedUnitSubspace hζ (Module.finBasis (ZMod p) k) c
  intro i
  rw [mem_primeUnitSubspace_iff]
  exact ordinaryFiniteRootClass_unit v p X E hζ hα he hβ
    ((Module.finBasis (ZMod p) k).coord i) hρ w hw

end ThreeAdicPlan
