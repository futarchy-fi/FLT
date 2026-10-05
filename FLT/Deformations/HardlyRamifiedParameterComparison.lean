/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFiniteParameters
public import FLT.Deformations.HardlyRamifiedFramedParameters

/-!
# Recovery frames preserve the finite kernel field

Restricting a framed HR coefficient map to the trace image preserves the
kernel, hence the finite field and its discriminant. This only compares
parameters that extend to the framed ring; it asserts no extension theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat MoritaReconstruction
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
local notation "T" => hardlyTraceImageObject O hp hdim ρ hρ
local notation "inc" => hardlyTraceImageInclusion O hp hdim ρ hρ

variable (hirr : ρ.IsIrreducible)

/-- The original strict recovery frame specializes over every coefficient target. -/
theorem hardlyParameter_recovery (A : ProartinianCat O) (f : H ⟶ A) (g : G) :
    Matrix.GeneralLinearGroup.map f.hom.toRingHom (hardlyTraceFrame O hp hdim ρ hρ hirr) *
      hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A (inc ≫ f) g *
      (Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (hardlyTraceFrame O hp hdim ρ hρ hirr))⁻¹ =
      hardlyFramedParameterRepresentation O hp hdim ρ hρ A f g := by
  have h := congrArg (Matrix.GeneralLinearGroup.map f.hom.toRingHom)
    (hardlyTraceLift_recovery O hp hdim ρ hρ hirr g)
  have hc (M : GL (Fin 2) T) :
      Matrix.GeneralLinearGroup.map (inc ≫ f).hom.toRingHom M =
        Matrix.GeneralLinearGroup.map f.hom.toRingHom
          (Matrix.GeneralLinearGroup.map (inc).hom.toRingHom M) := by
    apply Units.ext
    ext i j
    rfl
  simpa only [hardlyTraceParameterRepresentation, hardlyFramedParameterRepresentation,
    repnFunctor_map, hc, map_mul, map_inv] using h

/-- A recovery-frame change preserves the exact kernel of the finite representation. -/
theorem hardlyParameter_kernel_eq (A : ProartinianCat O) (f : H ⟶ A) :
    (hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A (inc ≫ f)).toMonoidHom.ker =
      (hardlyFramedParameterRepresentation O hp hdim ρ hρ A f).toMonoidHom.ker := by
  ext g
  change hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A (inc ≫ f) g = 1 ↔
    hardlyFramedParameterRepresentation O hp hdim ρ hρ A f g = 1
  rw [← hardlyParameter_recovery O hp hdim ρ hρ hirr A f g]
  simp only [mul_inv_eq_one, mul_eq_left]

/-- The actual finite Galois fields coincide for a parameter and its trace restriction. -/
theorem hardlyParameter_field_eq (A : ProartinianCat O) [DiscreteTopology A] (f : H ⟶ A) :
    hardlyTraceParameterField O hp hdim ρ hρ hirr A (inc ≫ f) =
      hardlyFramedParameterField O hp hdim ρ hρ A f := by
  apply FiniteGaloisIntermediateField.val_injective
  change IntermediateField.fixedField
    (hardlyTraceParameterRepresentation O hp hdim ρ hρ hirr A (inc ≫ f)).toMonoidHom.ker =
      IntermediateField.fixedField
        (hardlyFramedParameterRepresentation O hp hdim ρ hρ A f).toMonoidHom.ker
  rw [hardlyParameter_kernel_eq O hp hdim ρ hρ hirr A f]

/-- The discriminant comparison is for those same embedded fields. -/
theorem hardlyParameter_discr_eq (A : ProartinianCat O) [DiscreteTopology A] (f : H ⟶ A) :
    NumberField.discr (hardlyTraceParameterField O hp hdim ρ hρ hirr A (inc ≫ f)) =
      NumberField.discr (hardlyFramedParameterField O hp hdim ρ hρ A f) := by
  rw [hardlyParameter_field_eq O hp hdim ρ hρ hirr A f]

end Deformation
