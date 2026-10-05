/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TraceZeroPairing
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationTwist
public import FLT.GaloisRepresentation.SerreWeight.LocalCharacterNormalization
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The trace-zero adjoint and its Tate dual

The dual action is contragredient, then twisted by the specified character.
Evaluation is equivariant into that character line. In odd characteristic,
the trace pairing identifies the adjoint with its untwisted linear dual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation
open GaloisRepresentation.Extensions
variable {k G n : Type*} [Field k] [Group G] [Fintype n] [DecidableEq n]
  (r : G →* GL n k)

instance traceZeroAdjointSMulCommClass : SMulCommClass G k (traceZeroAdjoint r) where
  smul_comm g a X := by
    apply Subtype.ext
    exact (congrArg (fun Z : Matrix n n k ↦ adjointMatrixProduct Z (r g)⁻¹.val)
      (Matrix.mul_smul (r g).val a X.val)).trans (Matrix.smul_mul a _ _)

/-- The actual trace-zero action as a linear representation. -/
def traceZeroRepresentation : Representation k G (traceZeroAdjoint r) :=
  Representation.ofDistribMulAction k G (traceZeroAdjoint r)

/-- The Tate dual is the contragredient representation twisted by the cyclotomic character. -/
def adjointTateDual (χ : G →* kˣ) : Representation k G (Module.Dual k (traceZeroAdjoint r)) :=
  ordinaryTwistRepresentation (traceZeroRepresentation r).dual χ

/-- Evaluation transforms under the specified cyclotomic scalar, with the inverse action correct. -/
theorem adjointTateDual_evaluation (χ : G →* kˣ) (g : G)
    (f : Module.Dual k (traceZeroAdjoint r)) (X : traceZeroAdjoint r) :
    adjointTateDual r χ g f (g • X) = (χ g : k) * f X := by
  change (χ g : k) * f (g⁻¹ • (g • X)) = _
  rw [inv_smul_smul]

/-- Trace identifies the adjoint action with its contragredient action. -/
theorem traceZeroPairing_equivariant (g : G) (X : traceZeroAdjoint r) :
    traceZeroPairing r (g • X) = (traceZeroRepresentation r).dual g (traceZeroPairing r X) := by
  ext Y
  change traceZeroPairing r (g • X) Y = traceZeroPairing r X (g⁻¹ • Y)
  simpa only [smul_inv_smul] using traceZeroPairing_invariant r g X (g⁻¹ • Y)

/-- The local Tate dual uses the actual mod-p action on roots of unity. -/
def localAdjointTateDual (p : ℕ) [Fact p.Prime] (f : ZMod p →+* k)
    (ρ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      (LocalCyclotomic.rationalPlace p)) →* GL n k) :
    Representation k (Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)))
        (Module.Dual k (traceZeroAdjoint ρ)) :=
  adjointTateDual ρ ((Units.map f.toMonoidHom).comp
    (GaloisRepresentation.SerreWeight.localModCyclotomic p))

end Deformation

namespace Deformation
variable {k G : Type*} [Field k] [Group G] (r : G →* GL (Fin 2) k)

/-- The actual adjoint matrix space is finite dimensional. -/
instance traceZeroAdjointFinite : Module.Finite k (traceZeroAdjoint r) := by
  let : Module.Finite k (AdjointMatrices r) :=
    inferInstanceAs (Module.Finite k (Matrix (Fin 2) (Fin 2) k))
  exact inferInstance

/-- Perfectness of the rank-two trace pairing, without an assumed duality field. -/
def traceZeroDualEquiv (h2 : (2 : k) ≠ 0) :
    traceZeroAdjoint r ≃ₗ[k] Module.Dual k (traceZeroAdjoint r) :=
  LinearEquiv.ofBijective (traceZeroPairing r)
    ⟨traceZeroPairing_injective r h2,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := k) (V := traceZeroAdjoint r)).symm).mp
          (traceZeroPairing_injective r h2)⟩

/-- The equivalence preserves the specified Galois action. -/
theorem traceZeroDualEquiv_equivariant (h2 : (2 : k) ≠ 0) (g : G) (X : traceZeroAdjoint r) :
    traceZeroDualEquiv r h2 (g • X) =
      (traceZeroRepresentation r).dual g (traceZeroDualEquiv r h2 X) :=
  traceZeroPairing_equivariant r g X

end Deformation
