/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrimeDiagonalPoints
public import FLT.GroupScheme.LocalModelIdentification
public import FLT.GroupScheme.OrdinaryFiltrationModels

/-!
# The actual ordinary integral kernel is diagonalizable

For a prime-field cyclotomic subcharacter in small ramification, local
uniqueness identifies the original schematic kernel with the cyclic group
algebra, preserving the specified primitive-root point coordinates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions KummerTheory
namespace ThreeAdicPlan

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module (ZMod p) X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) (ZMod p) X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* (ZMod p)ˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction (ZMod p)
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hα : α = primeCyclotomicCharacter hζ)

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

/-- The prescribed generic comparison uses the original kernel coordinate. -/
def ordinaryDiagonalGeneric : GenericGaloisHom (ordinaryKernelModel X E)
    (diagonalGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) (ZMod p)) := by
  let f : CharacterModule α (ZMod p) →+
      (diagonalGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) (ZMod p)).Points :=
    AddMonoidHom.mk' (primeDiagonalPoint (v.adicCompletionIntegers K) (v.adicCompletion K) hζ)
      (primeDiagonalPoint_add (v.adicCompletionIntegers K) (v.adicCompletion K) hζ)
  refine { f with map_smul' := ?_ }
  intro g x
  change ZMod p at x
  change primeDiagonalPoint (v.adicCompletionIntegers K) (v.adicCompletion K) hζ
    ((α g : ZMod p) * x) = g • primeDiagonalPoint _ _ hζ x
  rw [hα]
  exact primeDiagonalPoint_equivariant _ _ hζ g x

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

/-- The integral isomorphism is on the actual schematic kernel. -/
def ordinaryLocalDiagonalIso : (ordinaryKernelModel X E).Iso
    (diagonalGroupModel (v.adicCompletionIntegers K) (v.adicCompletion K) (ZMod p)) :=
  (existsUnique_iso_of_local_killed v p he
    (fun x ↦ by
      change p • (show ZMod p from x) = 0
      simp [nsmul_eq_mul, CharP.cast_eq_zero])
    (ordinaryDiagonalGeneric v p X E hζ hα)
    (primeDiagonalPoint_bijective (v.adicCompletionIntegers K) (v.adicCompletion K) hζ)).choose

/-- The integral comparison retains the chosen root coordinates on every point. -/
theorem ordinaryLocalDiagonalIso_point (x : ZMod p) :
    genericHom (ordinaryLocalDiagonalIso v p X E hζ hα he).toBialgHom x =
      primeDiagonalPoint (v.adicCompletionIntegers K) (v.adicCompletion K) hζ x := by
  exact DFunLike.congr_fun
    (existsUnique_iso_of_local_killed v p he
      (fun x ↦ by
        change p • (show ZMod p from x) = 0
        simp [nsmul_eq_mul, CharP.cast_eq_zero])
      (ordinaryDiagonalGeneric v p X E hζ hα)
      (primeDiagonalPoint_bijective
        (v.adicCompletionIntegers K) (v.adicCompletion K) hζ)).choose_spec.1
    x

/-- Evaluation on transported group-like coordinates is the prescribed root power. -/
theorem ordinaryLocalDiagonalIso_single (x a : ZMod p) :
    (ordinaryKernelModel X E).integralPoints x
      (ordinaryLocalDiagonalIso v p X E hζ hα he
        (MonoidAlgebra.single (Multiplicative.ofAdd a) 1)) =
      (rootUnit (primeRootCoordinates hζ (x * a)) : AlgebraicClosure (v.adicCompletion K)) := by
  have h := integralPoints_genericHom
    (ordinaryLocalDiagonalIso v p X E hζ hα he).toBialgHom x
  rw [ordinaryLocalDiagonalIso_point] at h
  exact (AlgHom.congr_fun h (MonoidAlgebra.single (Multiplicative.ofAdd a) 1)).symm.trans
    (primeDiagonalPoint_single _ _ hζ x a)

end ThreeAdicPlan
