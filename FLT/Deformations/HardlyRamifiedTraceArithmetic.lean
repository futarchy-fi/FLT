/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceLift

/-!
# Arithmetic equations on the lift over the HR trace image

Injectivity of the image inclusion descends the cyclotomic determinant and
unramifiedness away from 2p. Finite flatness over the image is a separate
integral descent obligation, not a consequence of this ring injection.
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

/-- The representation constructed on the actual image of unframed coefficients. -/
def hardlyTraceLift : ContinuousFramedLifts O G (Fin 2) r T :=
  (exists_hardlyTraceImageLift O hp hdim ρ hρ hirr).choose

/-- The constructed frame over the original HR quotient. -/
def hardlyTraceFrame : GL (Fin 2) H :=
  (exists_hardlyTraceImageLift O hp hdim ρ hρ hirr).choose_spec.choose

/-- This frame reduces to the identity, retaining the specified residual basis. -/
theorem hardlyTraceFrame_residue :
    Matrix.GeneralLinearGroup.map (toResidueField H).hom.toRingHom
      (hardlyTraceFrame O hp hdim ρ hρ hirr) = 1 :=
  (exists_hardlyTraceImageLift O hp hdim ρ hρ hirr).choose_spec.choose_spec.1

/-- Scalar extension and the constructed frame recover the same HR lift. -/
theorem hardlyTraceLift_recovery (g : G) :
    hardlyTraceFrame O hp hdim ρ hρ hirr * Matrix.GeneralLinearGroup.map
      (inc).hom.toRingHom ((hardlyTraceLift O hp hdim ρ hρ hirr).val g) *
      (hardlyTraceFrame O hp hdim ρ hρ hirr)⁻¹ =
        (hardlyFlatLift O hp hdim ρ hρ).val g :=
  (exists_hardlyTraceImageLift O hp hdim ρ hρ hirr).choose_spec.choose_spec.2 g

/-- The representation over the image has the original cyclotomic determinant. -/
theorem hardlyTraceLift_det (g : G) :
    ((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.det =
      algebraMap O T (hardlyCyclotomicValue (p := p) O g) := by
  apply hardlyTraceImageInclusion_injective O hp hdim ρ hρ
  have h := congrArg (fun M : GL (Fin 2) H ↦ M.val.det)
    (hardlyTraceLift_recovery O hp hdim ρ hρ hirr g)
  change Matrix.det ((hardlyTraceFrame O hp hdim ρ hρ hirr).val *
    (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.map (inc).hom) *
    ((hardlyTraceFrame O hp hdim ρ hρ hirr)⁻¹).val) = _ at h
  rw [Matrix.det_units_conj] at h
  have hd := RingHom.map_det (inc).hom.toRingHom
    ((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val
  exact hd.trans (h.trans ((hardlyFlatLift_det O hp hdim ρ hρ g).trans
    ((inc).hom.commutes _).symm))

/-- Arithmetic inertia away from 2p acts trivially already over the trace image. -/
theorem hardlyTraceLift_inertia (g : G) (hg : g ∈ hardlyAwayInertia p) :
    (hardlyTraceLift O hp hdim ρ hρ hirr).val g = 1 := by
  have ht := (trivial_hardlyAwayInertia_iff p
    (FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val)).mpr
    (hardlyFlatLift_unramified O hp hdim ρ hρ)
  have he : (hardlyFlatLift O hp hdim ρ hρ).val g = 1 := by
    simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using ht g hg
  have h := hardlyTraceLift_recovery O hp hdim ρ hρ hirr g
  rw [he] at h
  have hc : Matrix.GeneralLinearGroup.map (inc).hom.toRingHom
      ((hardlyTraceLift O hp hdim ρ hρ hirr).val g) = 1 := by
    apply mul_left_cancel (a := hardlyTraceFrame O hp hdim ρ hρ hirr)
    apply mul_right_cancel (b := (hardlyTraceFrame O hp hdim ρ hρ hirr)⁻¹)
    simpa using h
  apply Units.ext
  ext i j
  apply hardlyTraceImageInclusion_injective O hp hdim ρ hρ
  have hij := congrArg (fun M : GL (Fin 2) H ↦ M i j) hc
  change (inc).hom (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val i j) =
    (1 : Matrix (Fin 2) (Fin 2) H) i j at hij
  simp only [Units.val_one, Matrix.one_apply] at hij ⊢
  split_ifs at hij ⊢
  · exact hij.trans ((inc).hom.map_one).symm
  · exact hij.trans ((inc).hom.map_zero).symm

/-- The image lift is unramified at every prime away from 2p. -/
theorem hardlyTraceLift_unramified (q : ℕ) (hq : q.Prime) (hgood : q ≠ 2 ∧ q ≠ p) :
    (FramedGaloisRep.ofGL (hardlyTraceLift O hp hdim ρ hρ hirr).val).IsUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat := by
  apply (trivial_hardlyAwayInertia_iff p _).mp ?_ q hq hgood
  intro g hg
  simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using
    hardlyTraceLift_inertia O hp hdim ρ hρ hirr g hg

end Deformation
