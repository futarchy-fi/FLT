/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTracePoint
public import FLT.Deformations.ArithmeticGaloisQuotient

/-!
# The original HR representations on the arithmetic quotient

Apply the quotient's proved universal property to the original residual,
framed HR lift, and trace-image lift. The local restriction at two retains
the same embedding and exact quotient row.
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

/-- The original residual representation factors through the arithmetic group. -/
def hardlyArithmeticResidual : HardlyArithmeticGaloisGroup p →ₜ*
    GL (Fin 2) (residueField (𝓞 := O)) :=
  hardlyArithmeticGaloisDescend p r (hardlyTwoFramedResidual_away O hp hdim ρ hρ)

/-- The universal framed HR lift factors through the same arithmetic group. -/
def hardlyArithmeticFramedLift : HardlyArithmeticGaloisGroup p →ₜ* GL (Fin 2) H :=
  hardlyArithmeticGaloisDescend p (hardlyFlatLift O hp hdim ρ hρ).val
    (by simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using
      (trivial_hardlyAwayInertia_iff p
        (FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val)).mpr
          (hardlyFlatLift_unramified O hp hdim ρ hρ))

/-- The quotient-adapted trace-image lift factors through that same arithmetic group. -/
def hardlyArithmeticTraceLift : HardlyArithmeticGaloisGroup p →ₜ* GL (Fin 2) T :=
  hardlyArithmeticGaloisDescend p (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val
    (hardlyTraceShearedLift_inertia O hp hdim ρ hρ hirr)

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))] in
/-- Residual descent preserves each original matrix. -/
theorem hardlyArithmeticResidual_apply (g : G) :
    hardlyArithmeticResidual O hp hdim ρ hρ (hardlyArithmeticGaloisProjection p g) = r g := rfl

/-- Framed descent preserves each original universal matrix. -/
theorem hardlyArithmeticFramedLift_apply (g : G) :
    hardlyArithmeticFramedLift O hp hdim ρ hρ (hardlyArithmeticGaloisProjection p g) =
      (hardlyFlatLift O hp hdim ρ hρ).val g := rfl

/-- Localizing the descended trace lift retains exactly the specified quotient at two. -/
theorem hardlyArithmeticTraceLift_two (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    hardlyArithmeticTraceLift O hp hdim ρ hρ hirr
      (hardlyArithmeticGaloisProjection p
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)) 1 j =
      if j = 1 then algebraMap O T (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
      else 0 :=
  hardlyTraceShearedLift_row O hp hdim ρ hρ hirr g j

end Deformation
