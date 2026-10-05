/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceArithmetic
public import FLT.Deformations.HardlyRamifiedTwoFrobenius
public import FLT.Deformations.RepresentationTheory.NormalizedQuotientDescent

/-!
# The specified quotient at two over the actual trace image

The residual Frobenius gap is a unit. It determines a normalized quotient
row over the trace image, whose equivariance descends from the recovery frame.
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

/-- The specified quadratic quotient descends, with its original residual row. -/
theorem exists_hardlyTraceTwoRow :
    ∃ t : T, (toResidueField T).hom t = 0 ∧
      (inc).hom t * hardlyTraceFrame O hp hdim ρ hρ hirr 1 1 =
        hardlyTraceFrame O hp hdim ρ hρ hirr 1 0 ∧
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2),
        t * (hardlyTraceLift O hp hdim ρ hρ hirr).val
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 0 j +
        (hardlyTraceLift O hp hdim ρ hρ hirr).val
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
            algebraMap O T (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) *
              (if j = 0 then t else 1) := by
  let P := hardlyTraceFrame O hp hdim ρ hρ hirr
  have hP (i j : Fin 2) : (toResidueField H).hom (P i j) =
      (1 : Matrix (Fin 2) (Fin 2) (residueField (𝓞 := O))) i j :=
    congrArg (fun X : GL (Fin 2) (residueField (𝓞 := O)) ↦ X i j)
      (hardlyTraceFrame_residue O hp hdim ρ hρ hirr)
  have hb : IsUnit (P 1 1) := by
    apply isUnit_of_map_unit (toResidueField H).hom
    rw [hP]
    simp
  obtain ⟨g₀, hg₀⟩ := exists_hardlyTwoResidual_gap O hp hdim ρ hρ
  let M := fun g : Field.absoluteGaloisGroup ℚ_[2] ↦
    ((hardlyTraceLift O hp hdim ρ hρ hirr).val
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)).val
  let χ := fun g ↦ algebraMap O T (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
  have hred (s : G) (i j : Fin 2) :
      (toResidueField T).hom ((hardlyTraceLift O hp hdim ρ hρ hirr).val s i j) = r s i j :=
    congrArg (fun t : G →* GL (Fin 2) (residueField (𝓞 := O)) ↦ t s i j)
      (hardlyTraceLift O hp hdim ρ hρ hirr).property
  have hd : IsUnit (M g₀ 0 0 - χ g₀) := by
    apply isUnit_of_map_unit (toResidueField T).hom
    change IsUnit ((toResidueField T).hom (_ - _))
    rw [map_sub, hred]
    dsimp only [χ]
    erw [(toResidueField T).hom.commutes]
    exact hg₀
  have heigen : ∀ g j, P 1 0 * (inc).hom (M g 0 j) +
      P 1 1 * (inc).hom (M g 1 j) = (inc).hom (χ g) *
        (if j = 0 then P 1 0 else P 1 1) := by
    intro g j
    have he := recoveryFrame_eigenrow P
      (Matrix.GeneralLinearGroup.map (inc).hom.toRingHom
        ((hardlyTraceLift O hp hdim ρ hρ hirr).val
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)))
      ((hardlyFlatLift O hp hdim ρ hρ).val
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g))
      (algebraMap O H (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O))
      (hardlyTraceLift_recovery O hp hdim ρ hρ hirr _)
      (hardlyFlatLift_row O hp hdim ρ hρ g) j
    change _ + _ = (inc).hom (χ g) * _
    dsimp only [χ]
    erw [(inc).hom.commutes]
    fin_cases j <;> simpa [M] using he
  obtain ⟨t, ht, he⟩ := exists_normalizedQuotient_descent (inc).hom.toRingHom
    (hardlyTraceImageInclusion_injective O hp hdim ρ hρ) M χ (P 1 0) (P 1 1) hb
    heigen g₀ hd
  refine ⟨t, ?_, ht, he⟩
  have hr := congrArg (toResidueField H).hom ht
  rw [map_mul, hP, hP] at hr
  have hf : inc ≫ toResidueField H = toResidueField T := Subsingleton.elim _ _
  change (inc ≫ toResidueField H).hom t * _ = _ at hr
  rw [hf] at hr
  simpa using hr

end Deformation
