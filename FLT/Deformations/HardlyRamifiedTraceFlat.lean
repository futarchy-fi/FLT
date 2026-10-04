/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceArithmetic
public import FLT.Deformations.RepresentationTheory.FlatCoefficientDescent
public import FLT.Deformations.RepresentationTheory.FlatMatrixConjugation

/-!
# Finite-flat descent to the actual HR trace image

The recovery frame identifies scalar extension with the framed HR lift.
Compactness makes the trace-image inclusion a topological embedding, and
schematic closure descends finite-flat models on a cofinal family of reductions.
This does not assert p-adic module finiteness or the KW local-ring comparison.
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

/-- The actual trace-image lift has finite-flat models on every open reduction. -/
theorem hardlyTraceLift_isFlat :
    (FramedGaloisRep.ofGL (hardlyTraceLift O hp hdim ρ hρ hirr).val).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) := by
  let sigma := FramedGaloisRep.ofGL (hardlyTraceLift O hp hdim ρ hρ hirr).val
  let tau := FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val
  apply FramedGaloisRep.isFlatAt_of_compact_injective _ sigma
    (inc).hom.toRingHom (inc).hom.cont
    (hardlyTraceImageInclusion_injective O hp hdim ρ hρ)
  apply (FramedGaloisRep.isFlatAt_iff_of_matrix_recovery
    (sigma.baseChange (inc).hom.toRingHom (inc).hom.cont) tau
    (hardlyTraceFrame O hp hdim ρ hρ hirr) ?_ _).mpr
    (hardlyFlatLift_isFlat O hp hdim ρ hρ)
  intro g
  have he : (sigma.baseChange (inc).hom.toRingHom (inc).hom.cont).GL g =
      Matrix.GeneralLinearGroup.map (inc).hom.toRingHom
        ((hardlyTraceLift O hp hdim ρ hρ hirr).val g) := by
    apply Units.ext
    ext i j
    simp only [sigma, FramedGaloisRep.baseChange_GL,
      FramedGaloisRep.ofGL, Equiv.apply_symm_apply]
    rfl
  rw [he]
  simpa only [tau, FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using
    hardlyTraceLift_recovery O hp hdim ρ hρ hirr g

/-- Every specialization of the trace lift retains its finite-flat reductions. -/
theorem hardlyTraceLift_specialization_isFlat (A : ProartinianCat O) (f : T ⟶ A) :
    ((FramedGaloisRep.ofGL (hardlyTraceLift O hp hdim ρ hρ hirr).val).baseChange
      f.hom.toRingHom f.hom.cont).IsFlatAt
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) :=
  flat_specialization T _ _ f (hardlyTraceLift_isFlat O hp hdim ρ hρ hirr)

end Deformation
