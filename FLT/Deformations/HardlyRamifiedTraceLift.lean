/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.IteratedBaseChangeIrreducible
public import FLT.Deformations.HardlyRamifiedTraceImage
public import FLT.Deformations.DeSmitLenstra.TraceImageLift
public import FLT.GaloisRepresentation.HardlyRamified.AbsoluteIrreducibility

/-!
# Descent of the actual HR lift to its trace image

Absolute irreducibility is proved from the original irreducible HR input.
The recovered frame has the original specified row at two. This does not
assert finiteness of the trace image or effective finite-flat descent to it.
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

omit [IsNoetherianRing O] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))] in
/-- The actual quotient-adapted residual frame is absolutely irreducible. -/
theorem hardlyTwoFramedResidual_absIrred (hirr : ρ.IsIrreducible) :
    (residualLinearRepresentation O G (Fin 2) r).IsAbsolutelyIrreducible.{0} := by
  let : Finite (residueField (𝓞 := O)) := inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  let b := (hardlyTwoFrame O hp hdim ρ hρ).symm
  let τ := ρ.conj b
  let eb : ρ.toRepresentation.Equiv τ.toRepresentation := .mk b (by
    intro g
    apply LinearMap.ext
    intro x
    change b (ρ g x) = b (ρ g (b.symm (b x)))
    rw [b.symm_apply_apply])
  have hd : Module.rank (residueField (𝓞 := O)) (Fin 2 → residueField (𝓞 := O)) = 2 := by
    simp
  have ha := (hρ.conj hp hdim hd b).isAbsolutelyIrreducible hp hd
    (eb.isIrreducible_iff.mp hirr)
  have he : τ.toRepresentation = residualLinearRepresentation O G (Fin 2) r := by
    change (ρ.conj b).toRepresentation =
      (toFramedGaloisRep r).toRepresentation
    change (ρ.conj b).toRepresentation =
      (FramedGaloisRep.GL.symm (FramedGaloisRep.GL (ρ.conj b))).toRepresentation
    rw [Equiv.symm_apply_apply]
  rwa [he] at ha

set_option maxHeartbeats 800000 in
-- The application unfolds the HR image and its universal specialization together.
/-- The same HR representation descends to the trace image with a strict recovery frame. -/
theorem exists_hardlyTraceImageLift (hirr : ρ.IsIrreducible) :
    ∃ sigma : ContinuousFramedLifts O G (Fin 2) r T,
      ∃ P : GL (Fin 2) H,
        Matrix.GeneralLinearGroup.map (toResidueField H).hom.toRingHom P = 1 ∧
        ∀ g, P * Matrix.GeneralLinearGroup.map (inc).hom.toRingHom (sigma.val g) * P⁻¹ =
          (hardlyFlatLift O hp hdim ρ hρ).val g := by
  let := hardlyTwoFramedResidual_absIrred O hp hdim ρ hρ hirr
  exact exists_traceImageLift O G (Fin 2) r H (hardlyFlatLift O hp hdim ρ hρ)

/-- In the recovered frame the specified quotient row at two is the original one. -/
theorem exists_hardlyTraceImageLift_with_row (hirr : ρ.IsIrreducible) :
    ∃ sigma : ContinuousFramedLifts O G (Fin 2) r T,
      ∃ P : GL (Fin 2) H,
        Matrix.GeneralLinearGroup.map (toResidueField H).hom.toRingHom P = 1 ∧
        (∀ g, P * Matrix.GeneralLinearGroup.map (inc).hom.toRingHom (sigma.val g) * P⁻¹ =
          (hardlyFlatLift O hp hdim ρ hρ).val g) ∧
        ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ j : Fin 2,
          (P * Matrix.GeneralLinearGroup.map (inc).hom.toRingHom
            (sigma.val (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)) * P⁻¹) 1 j =
              if j = 1 then algebraMap O H (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
              else 0 := by
  obtain ⟨sigma, P, hP, he⟩ := exists_hardlyTraceImageLift O hp hdim ρ hρ hirr
  exact ⟨sigma, P, hP, he, fun g j ↦ by
    rw [he]
    exact hardlyFlatLift_row O hp hdim ρ hρ g j⟩

end Deformation
