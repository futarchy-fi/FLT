/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTangentEquations
public import FLT.Deformations.RepresentationTheory.MatrixTangentTrace

/-!
# Continuous trace-zero cocycles from the actual HR tangent space

Normalize the derivative of the universal HR lift by the original residual
matrix. The result is a continuous adjoint cocycle satisfying trace zero and
the exact vanishing second row at two. Selmer-image equality is not asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "r" => hardlyTwoFramedResidual O hp hdim ρ hρ
local notation "H" => hardlyFlatObject O hp hdim ρ hρ
local notation "k" => residueField (𝓞 := O)

variable (d : continuousTangent O (hardlyFlatObject O hp hdim ρ hρ))

/-- Entrywise differentiation of the actual continuous lift is continuous. -/
theorem hardlyTangentMatrix_continuous :
    Continuous (hardlyTangentMatrix O hp hdim ρ hρ d) := by
  apply continuous_matrix
  intro i j
  exact d.1.continuous.comp
    ((Units.continuous_val.comp (hardlyFlatLift O hp hdim ρ hρ).val.continuous).matrix_elem i j)

/-- The actual tangent functional gives a continuous cocycle for the residual adjoint action. -/
def hardlyTangentCocycle :
    Extensions.ContinuousCocycle G (AdjointMatrices (r).toMonoidHom) :=
  matrixDerivativeCocycle (r).toMonoidHom (hardlyTangentMatrix O hp hdim ρ hρ d)
    (r).continuous (hardlyTangentMatrix_continuous O hp hdim ρ hρ d)
    (hardlyTangentMatrix_mul O hp hdim ρ hρ d)

/-- Its value is the right-normalized derivative with no new choice of residual model. -/
theorem hardlyTangentCocycle_apply (g : G) :
    (hardlyTangentCocycle O hp hdim ρ hρ d).1 g =
      (show AdjointMatrices (r).toMonoidHom from
        hardlyTangentMatrix O hp hdim ρ hρ d g * (r g)⁻¹.val) := rfl

/-- The original fixed determinant puts every cocycle value in the trace-zero adjoint. -/
theorem hardlyTangentCocycle_trace_zero (g : G) :
    (hardlyTangentCocycle O hp hdim ρ hρ d).1 g ∈ traceZeroAdjoint (r).toMonoidHom :=
  trace_normalizedMatrixDerivative_eq_zero (r g) _
    (hardlyTangentMatrix_det O hp hdim ρ hρ d g)

/-- The exact quotient row remains zero after right normalization. -/
theorem hardlyTangentCocycle_two (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    (show Matrix (Fin 2) (Fin 2) k from (hardlyTangentCocycle O hp hdim ρ hρ d).1
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)) 1 j = 0 := by
  change (hardlyTangentMatrix O hp hdim ρ hρ d
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) *
      (r (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g))⁻¹.val) 1 j = 0
  simp only [Matrix.mul_apply, hardlyTangentMatrix_two, zero_mul, Finset.sum_const_zero]

/-- The cocycle takes values in the trace-zero adjoint itself, with its subspace topology. -/
def hardlyTraceZeroTangentCocycle :
    Extensions.ContinuousCocycle G (traceZeroAdjoint (r).toMonoidHom) :=
  ⟨⟨fun g ↦ ⟨(hardlyTangentCocycle O hp hdim ρ hρ d).1 g,
      hardlyTangentCocycle_trace_zero O hp hdim ρ hρ d g⟩,
    (hardlyTangentCocycle O hp hdim ρ hρ d).1.continuous.subtype_mk _⟩,
    fun g h ↦ Subtype.ext ((hardlyTangentCocycle O hp hdim ρ hρ d).2 g h)⟩

end Deformation
