/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFlatLift
public import FLT.Deformations.ContinuousTangent

/-!
# First-order equations for the actual HR tangent space

Differentiate the same universal framed lift with a continuous tangent
functional. The resulting matrices satisfy the actual product rule, fixed
local row at two, and linearized determinant equation. Identifying their
strict-equivalence classes with arithmetic Selmer cohomology remains separate.
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

/-- Entrywise derivative of the actual universal HR representation. -/
def hardlyTangentMatrix (g : G) : Matrix (Fin 2) (Fin 2) k :=
  fun i j ↦ d.1 ((hardlyFlatLift O hp hdim ρ hρ).val g i j)

/-- Relative tangent functionals kill the original coefficient ring. -/
theorem hardlyTangent_base (a : O) : d.1 (algebraMap O H a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, d.2.1, smul_zero]

/-- The derivative has the original residual representation as its coefficient action. -/
theorem hardlyTangentMatrix_mul (g h : G) :
    hardlyTangentMatrix O hp hdim ρ hρ d (g * h) =
      (r g).val * hardlyTangentMatrix O hp hdim ρ hρ d h +
        hardlyTangentMatrix O hp hdim ρ hρ d g * (r h).val := by
  have hr (s : G) (i j : Fin 2) : (toResidueField H).hom
      ((hardlyFlatLift O hp hdim ρ hρ).val s i j) = r s i j :=
    congrArg (fun t : G →* GL (Fin 2) k ↦ t s i j)
      (hardlyFlatLift O hp hdim ρ hρ).property
  ext i j
  simp only [hardlyTangentMatrix, map_mul, Units.val_mul, Matrix.mul_apply,
    Matrix.add_apply, map_sum, d.2.2, Finset.sum_add_distrib, hr]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

/-- Differentiation preserves the exact fixed quotient row at two. -/
theorem hardlyTangentMatrix_two (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    hardlyTangentMatrix O hp hdim ρ hρ d
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j = 0 := by
  unfold hardlyTangentMatrix
  rw [hardlyFlatLift_row]
  split_ifs
  · exact hardlyTangent_base O hp hdim ρ hρ d _
  · exact map_zero d.1

/-- The actual fixed determinant supplies its linearized equation without a new hypothesis. -/
theorem hardlyTangentMatrix_det (g : G) :
    r g 0 0 * hardlyTangentMatrix O hp hdim ρ hρ d g 1 1 +
      r g 1 1 * hardlyTangentMatrix O hp hdim ρ hρ d g 0 0 -
      (r g 0 1 * hardlyTangentMatrix O hp hdim ρ hρ d g 1 0 +
        r g 1 0 * hardlyTangentMatrix O hp hdim ρ hρ d g 0 1) = 0 := by
  have hr (i j : Fin 2) : (toResidueField H).hom
      ((hardlyFlatLift O hp hdim ρ hρ).val g i j) = r g i j :=
    congrArg (fun t : G →* GL (Fin 2) k ↦ t g i j)
      (hardlyFlatLift O hp hdim ρ hρ).property
  have he := congrArg d.1 (hardlyFlatLift_det O hp hdim ρ hρ g)
  rw [hardlyTangent_base O hp hdim ρ hρ d] at he
  simpa only [Matrix.det_fin_two, map_sub, d.2.2, hr, hardlyTangentMatrix] using he

end Deformation
