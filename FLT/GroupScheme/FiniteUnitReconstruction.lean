/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteRootProjection
public import FLT.GaloisRepresentation.Extensions.ExtendedUnitSubspace

/-!
# Reconstructing unit classes from prime-linear projections

Finite basis reconstruction expresses the original residual-field class as
a sum of extensions of its root-valued projections. The target is the existing
basis-independent span of integral Kummer unit classes.
-/

@[expose] public noncomputable section
namespace KummerTheory
open GaloisRepresentation.Extensions

variable {K L k ι : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {p : ℕ} [Fact p.Prime] [Field k] [Algebra (ZMod p) k]
  {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) [Fintype ι] (b : Module.Basis ι (ZMod p) k)
  (c : ContinuousCocycle Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k))

omit [IsGalois K L] in
/-- Reconstruct the actual cocycle class from prime-root projections in any finite basis. -/
theorem finiteRootClass_reconstruction :
    (Submodule.Quotient.mk (linearCocycleOf c) :
      LinearContinuousClass k Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) =
      ∑ i, b i • extendRootClass hζ k
        (Submodule.Quotient.mk (linearCocycleOf (finiteRootCocycle hζ (b.coord i) c))) := by
  change (continuousPrincipals k Gal(L/K)
    (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)).mkQ _ =
      ∑ i, b i • (continuousPrincipals k Gal(L/K)
        (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)).mkQ _
  simp only [← map_smul, ← map_sum]
  congr 1
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply]
  let x : k := c.1 g
  change x = ∑ i, b i * algebraMap (ZMod p) k
    ((primeRootCoordinates hζ).symm
      (primeRootCoordinates hζ (b.coord i x)))
  simp only [AddEquiv.symm_apply_apply]
  refine (b.sum_repr x).symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact (Algebra.smul_def ((b.repr x) i) (b i)).trans (mul_comm _ _)

variable (roots : ∀ q : Kˣ, ∃ z : Lˣ, z ^ p = Units.map (algebraMap K L) q)
  (A : ValuationSubring K)

omit [Fintype ι] in
/-- Integral unit projections imply membership in the independently defined extended unit space. -/
theorem finiteRootProjections_mem_extendedUnitSubspace [Finite ι]
    (hc : ∀ i, Submodule.Quotient.mk (linearCocycleOf (finiteRootCocycle hζ (b.coord i) c)) ∈
      primeUnitSubspace roots A) :
    (Submodule.Quotient.mk (linearCocycleOf c) :
      LinearContinuousClass k Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) ∈
      extendedUnitSubspace hζ k roots A := by
  let := Fintype.ofFinite ι
  rw [finiteRootClass_reconstruction hζ b c]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (extendRootClass_mem hζ k roots A (hc i))

end KummerTheory
