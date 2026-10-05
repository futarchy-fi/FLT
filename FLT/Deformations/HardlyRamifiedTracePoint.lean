/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceShear
public import FLT.Deformations.HardlyRamifiedFlatPoint

/-!
# A point of the framed HR ring over its trace image

The strict shear supplies the exact quotient row required by the universal
property. Determinant, unramifiedness and finite flatness survive this frame.
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

/-- The shear preserves the original determinant. -/
theorem hardlyTraceShearedLift_det (g : G) :
    ((hardlyTraceShearedLift O hp hdim ρ hρ hirr).val g).val.det =
      algebraMap O T (hardlyCyclotomicValue (p := p) O g) := by
  rw [hardlyTraceShearedLift_apply]
  exact (Matrix.det_units_conj _ _).trans (hardlyTraceLift_det O hp hdim ρ hρ hirr g)

/-- The shear preserves trivial arithmetic inertia. -/
theorem hardlyTraceShearedLift_inertia (g : G) (hg : g ∈ hardlyAwayInertia p) :
    (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val g = 1 := by
  rw [hardlyTraceShearedLift_apply, hardlyTraceLift_inertia O hp hdim ρ hρ hirr g hg]
  simp

/-- The quotient-adapted representation is unramified away from 2p. -/
theorem hardlyTraceShearedLift_unramified (q : ℕ) (hq : q.Prime)
    (hgood : q ≠ 2 ∧ q ≠ p) :
    (FramedGaloisRep.ofGL (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val).IsUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat := by
  apply (trivial_hardlyAwayInertia_iff p _).mp ?_ q hq hgood
  intro g hg
  simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using
    hardlyTraceShearedLift_inertia O hp hdim ρ hρ hirr g hg

/-- All finite-flat reductions persist in the quotient-adapted frame. -/
theorem hardlyTraceShearedLift_isFlat :
    (FramedGaloisRep.ofGL (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) := by
  apply (FramedGaloisRep.isFlatAt_iff_of_matrix_recovery
    (FramedGaloisRep.ofGL (hardlyTraceLift O hp hdim ρ hρ hirr).val)
    (FramedGaloisRep.ofGL (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val)
    (hardlyTraceShear O hp hdim ρ hρ hirr)
    ?_ _).mp (hardlyTraceLift_isFlat O hp hdim ρ hρ hirr)
  intro g
  simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using
    (hardlyTraceShearedLift_apply O hp hdim ρ hρ hirr g).symm

/-- The exact fixed-row lift gives a map back to the actual trace image. -/
def hardlyTracePoint : H ⟶ T :=
  hardlyFlatPoint O hp hdim ρ hρ T (hardlyTraceShearedLift O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_det O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_unramified O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_row O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_isFlat O hp hdim ρ hρ hirr)

/-- Specializing the framed HR lift along this point recovers the sheared lift. -/
theorem hardlyTracePoint_apply (g : G) (i j : Fin 2) :
    (hardlyTracePoint O hp hdim ρ hρ hirr).hom
      ((hardlyFlatLift O hp hdim ρ hρ).val g i j) =
        (hardlyTraceShearedLift O hp hdim ρ hρ hirr).val g i j := by
  have hc := hardlyFlatPoint_comp O hp hdim ρ hρ T
    (hardlyTraceShearedLift O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_det O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_unramified O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_row O hp hdim ρ hρ hirr)
    (hardlyTraceShearedLift_isFlat O hp hdim ρ hρ hirr)
  have he := congrArg (fun f ↦ (hardlyArithmeticEquiv O hp hdim ρ hρ T f).val.val g i j) hc
  rw [hardlyFlatLift, hardlyArithmeticEquiv_apply]
  simpa only [hardlyTracePoint, ProartinianCat.hom_comp, ContinuousAlgHom.comp_apply,
    hardlyArithmeticEquiv_apply, hardlyArithmeticPoint,
    Equiv.apply_symm_apply] using he

end Deformation
