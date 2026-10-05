/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceTwoQuotient
public import FLT.Deformations.RepresentationTheory.NormalizedQuotientShear

/-!
# An exact quotient-adapted frame over the trace image

The descended normalized row defines a strict shear over the smaller ring.
Conjugating by it fixes the original quotient row without changing traces.
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

/-- The strict quotient-adapted frame is defined over the trace image itself. -/
def hardlyTraceShear : GL (Fin 2) T :=
  normalizedQuotientShear (hardlyTraceTwoParameter O hp hdim ρ hρ hirr)

/-- The shear retains the original residual basis. -/
theorem hardlyTraceShear_residue :
    Matrix.GeneralLinearGroup.map (toResidueField T).hom.toRingHom
      (hardlyTraceShear O hp hdim ρ hρ hirr) = 1 :=
  normalizedQuotientShear_map _ _ (hardlyTraceTwoParameter_residue O hp hdim ρ hρ hirr)

/-- The same trace lift in its exact quotient-adapted frame. -/
def hardlyTraceShearedLift : ContinuousFramedLifts O G (Fin 2) r T := by
  let P := hardlyTraceShear O hp hdim ρ hρ hirr
  let σ := hardlyTraceLift O hp hdim ρ hρ hirr
  let τ : G →ₜ* GL (Fin 2) T :=
    { toFun := fun g ↦ P * σ.val g * P⁻¹
      map_one' := by simp
      map_mul' := fun g h ↦ by simp [mul_assoc]
      continuous_toFun := (continuous_const.mul σ.val.continuous).mul continuous_const }
  refine ⟨τ, ?_⟩
  have hP := hardlyTraceShear_residue O hp hdim ρ hρ hirr
  have hσ := σ.property
  unfold IsContinuousFramedLift at hσ ⊢
  ext g : 1
  change Matrix.GeneralLinearGroup.map (toResidueField T).hom.toRingHom
    (P * σ.val g * P⁻¹) = r g
  rw [map_mul, map_mul, map_inv, hP, one_mul, inv_one, mul_one]
  exact DFunLike.congr_fun hσ g

/-- Conjugation is by this explicit shear, not a new existential frame. -/
theorem hardlyTraceShearedLift_apply (g : G) :
    (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val g =
      hardlyTraceShear O hp hdim ρ hρ hirr *
        (hardlyTraceLift O hp hdim ρ hρ hirr).val g *
          (hardlyTraceShear O hp hdim ρ hρ hirr)⁻¹ := rfl

/-- The descended lift now has exactly the specified second row. -/
theorem hardlyTraceShearedLift_row (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
        if j = 1 then algebraMap O T (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
        else 0 :=
  normalizedQuotientShear_row _ _ _ (hardlyTraceTwoParameter_row O hp hdim ρ hρ hirr g) j

/-- The explicit framing does not change the trace coefficients. -/
theorem hardlyTraceShearedLift_trace (g : G) :
    ((hardlyTraceShearedLift O hp hdim ρ hρ hirr).val g).val.trace =
      ((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.trace :=
  Matrix.trace_units_conj _ _

end Deformation
