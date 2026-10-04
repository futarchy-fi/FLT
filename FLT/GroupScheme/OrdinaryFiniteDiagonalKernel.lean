/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteDiagonalPoints
public import FLT.GroupScheme.LocalModelIdentification
public import FLT.GroupScheme.OrdinaryFiltrationModels

/-!
# The actual ordinary integral kernel is diagonalizable

For a finite residual coefficient field and scalar cyclotomic subcharacter,
local uniqueness identifies the original schematic kernel with the group
algebra of the prime-linear dual, preserving every functional evaluation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The prescribed generic comparison uses the original kernel coordinate. -/
def ordinaryFiniteDiagonalGeneric : GenericGaloisHom (ordinaryKernelModel X E)
    (diagonalGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K)
      (Module.Dual (ZMod p) k)) := by
  let f : k →+ (diagonalGroupModel (v.adicCompletionIntegers K)
      (v.adicCompletion K) (Module.Dual (ZMod p) k)).Points :=
    AddMonoidHom.mk'
      (finiteDiagonalPoint (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ)
      (finiteDiagonalPoint_add (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ)
  refine { f with map_smul' := ?_ }
  intro g x
  change k at x
  change finiteDiagonalPoint (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ
    ((α g : k) * x) = g • finiteDiagonalPoint (v.adicCompletionIntegers K)
      (v.adicCompletion K) k hζ x
  rw [hα]
  simpa [Algebra.smul_def] using finiteDiagonalPoint_equivariant
      (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ g x

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

/-- The integral isomorphism is on the actual schematic kernel. -/
def ordinaryFiniteDiagonalIso : (ordinaryKernelModel X E).Iso
    (diagonalGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K)
      (Module.Dual (ZMod p) k)) :=
  (existsUnique_iso_of_local_killed v p he
    (fun x ↦ by
      change p • (show k from x) = 0
      simp only [← Nat.cast_smul_eq_nsmul (ZMod p), CharP.cast_eq_zero, zero_smul])
    (ordinaryFiniteDiagonalGeneric v p X E hζ hα)
    (finiteDiagonalPoint_bijective (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ)).choose

/-- The integral comparison retains the chosen root coordinates on every point. -/
theorem ordinaryFiniteDiagonalIso_point (x : k) :
    genericHom (ordinaryFiniteDiagonalIso v p X E hζ hα he).toBialgHom x =
      finiteDiagonalPoint (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ x := by
  exact DFunLike.congr_fun
    (existsUnique_iso_of_local_killed v p he
      (fun x ↦ by
        change p • (show k from x) = 0
        simp only [← Nat.cast_smul_eq_nsmul (ZMod p), CharP.cast_eq_zero, zero_smul])
      (ordinaryFiniteDiagonalGeneric v p X E hζ hα)
      (finiteDiagonalPoint_bijective
        (v.adicCompletionIntegers K) (v.adicCompletion K) k hζ)).choose_spec.1
    x

/-- Evaluation on transported group-like coordinates is the prescribed root power. -/
theorem ordinaryFiniteDiagonalIso_single (x : k) (a : Module.Dual (ZMod p) k) :
    (ordinaryKernelModel X E).integralPoints x
      (ordinaryFiniteDiagonalIso v p X E hζ hα he
        (MonoidAlgebra.single (Multiplicative.ofAdd a) 1)) =
      (rootUnit (primeRootCoordinates hζ (a x)) : AlgebraicClosure (v.adicCompletion K)) := by
  have h := integralPoints_genericHom
    (ordinaryFiniteDiagonalIso v p X E hζ hα he).toBialgHom x
  rw [ordinaryFiniteDiagonalIso_point] at h
  exact (AlgHom.congr_fun h (MonoidAlgebra.single (Multiplicative.ofAdd a) 1)).symm.trans
    (finiteDiagonalPoint_single _ _ k hζ x a)

end ThreeAdicPlan
