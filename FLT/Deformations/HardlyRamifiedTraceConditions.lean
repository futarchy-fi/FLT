/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceTwoQuotient
public import FLT.Deformations.RepresentationTheory.ScalarQuotient
public import FLT.GaloisRepresentation.HardlyRamified.SpecifiedTwoQuotient

/-!
# All hardly-ramified conditions on the trace-image lift

The descended quotient has the original unramified quadratic character.
Together with finite-flat descent, this verifies the complete HR predicate
after every compatible coefficient specialization. Coefficient finiteness
and characteristic zero are not asserted.
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

variable (A : ProartinianCat O) (f : hardlyTraceImageObject O hp hdim ρ hρ ⟶ A)
/-- The actual trace-image representation specialized along a coefficient morphism. -/
def hardlyTraceSpecializedRepresentation : FramedGaloisRep ℚ A (Fin 2) :=
  toFramedGaloisRep ((repnFunctor (Fin 2) G O).map f
    (hardlyTraceLift O hp hdim ρ hρ hirr).val)

local notation "τ" => hardlyTraceSpecializedRepresentation O hp hdim ρ hρ hirr A f

/-- The fixed integral character, in the specialized coefficient ring. -/
def hardlyTraceTwoScalar : Field.absoluteGaloisGroup ℚ_[2] →* A :=
  (algebraMap O A).toMonoidHom.comp
    ((Units.coeHom O).comp (hardlyTwoIntegralCharacter O hp hdim ρ hρ))

include hirr f in
/-- The descended quotient proves continuity of that same scalar character. -/
theorem hardlyTraceTwoScalar_continuous :
    Continuous (hardlyTraceTwoScalar O hp hdim ρ hρ A) :=
  continuous_scalar_of_quotient ((τ).map (algebraMap ℚ ℚ_[2]))
    (hardlyTraceTwoQuotient O hp hdim ρ hρ hirr A f)
    (hardlyTraceTwoQuotient_surjective O hp hdim ρ hρ hirr A f) _
    (hardlyTraceTwoQuotient_equivariant O hp hdim ρ hρ hirr A f)

/-- The continuous rank-one representation is fixed by the original quotient character. -/
def hardlyTraceTwoAction : GaloisRep ℚ_[2] A A :=
  continuousScalarGaloisRep (hardlyTraceTwoScalar O hp hdim ρ hρ A)
    (hardlyTraceTwoScalar_continuous O hp hdim ρ hρ hirr A f)

/-- The constructed action retains the exact specified quotient predicate. -/
theorem hardlyTrace_hasSpecifiedQuotientAtTwo :
    HasSpecifiedQuotientAtTwo τ (hardlyTraceTwoAction O hp hdim ρ hρ hirr A f) :=
  ⟨hardlyTraceTwoQuotient O hp hdim ρ hρ hirr A f,
    hardlyTraceTwoQuotient_surjective O hp hdim ρ hρ hirr A f,
    hardlyTraceTwoQuotient_equivariant O hp hdim ρ hρ hirr A f⟩

/-- The quotient action is unramified for the original inertia subgroup at two. -/
theorem hardlyTraceTwoAction_inertia (g : Field.absoluteGaloisGroup ℚ_[2])
    (hg : g ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    hardlyTraceTwoAction O hp hdim ρ hρ hirr A f g = 1 := by
  apply LinearMap.ext
  intro x
  change algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) * x = x
  rw [hardlyTwoIntegralCharacter_unramified O hp hdim ρ hρ g hg]
  simp

/-- The quotient action is quadratic over the integral coefficients themselves. -/
theorem hardlyTraceTwoAction_sq (g : Field.absoluteGaloisGroup ℚ_[2]) :
    hardlyTraceTwoAction O hp hdim ρ hρ hirr A f g *
      hardlyTraceTwoAction O hp hdim ρ hρ hirr A f g = 1 := by
  have hc := congrArg (fun u : Oˣ ↦ algebraMap O A (u : O))
    (quadraticCharacterLift_sq (hardlyTwoCharacter O hp hdim ρ hρ)
      (hardlyTwoCharacter_sq O hp hdim ρ hρ) O g)
  have hs : algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) ^ 2 = 1 := by
    simpa only [hardlyTwoIntegralCharacter, Units.val_pow_eq_pow_val, map_pow,
      Units.val_one, map_one] using hc
  apply LinearMap.ext
  intro x
  change algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) *
    (algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) * x) = x
  rw [← mul_assoc, ← pow_two, hs, one_mul]

variable [Algebra ℤ_[p] A] [IsScalarTower ℤ_[p] O A]

/-- Every compatible specialization of the actual trace lift is hardly ramified. -/
theorem hardlyTraceSpecializedRepresentation_isHardlyRamified :
    IsHardlyRamified hp (by simp : Module.rank A (Fin 2 → A) = 2) τ := by
  constructor
  · intro g
    change LinearMap.det ((τ) g) = _
    rw [← LinearMap.det_toMatrix']
    rw [← FramedGaloisRep.GL_apply]
    simp only [hardlyTraceSpecializedRepresentation, toFramedGaloisRep,
      Equiv.apply_symm_apply]
    change Matrix.det (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.map f.hom) = _
    exact (RingHom.map_det f.hom.toRingHom _).symm.trans
      ((congrArg f.hom (hardlyTraceLift_det O hp hdim ρ hρ hirr g)).trans
        ((f.hom.commutes _).trans (IsScalarTower.algebraMap_apply ℤ_[p] O A _).symm))
  · intro q hq hgood
    apply (trivial_hardlyAwayInertia_iff p _).mp ?_ q hq hgood
    intro g hg
    simp only [hardlyTraceSpecializedRepresentation, toFramedGaloisRep,
      Equiv.apply_symm_apply]
    change Matrix.GeneralLinearGroup.map f.hom.toRingHom
      ((hardlyTraceLift O hp hdim ρ hρ hirr).val g) = 1
    rw [hardlyTraceLift_inertia O hp hdim ρ hρ hirr g hg, map_one]
  · unfold hardlyTraceSpecializedRepresentation
    rw [toFramedGaloisRep_map]
    exact hardlyTraceLift_specialization_isFlat O hp hdim ρ hρ hirr A f
  · obtain ⟨q, hq, he⟩ := hardlyTrace_hasSpecifiedQuotientAtTwo O hp hdim ρ hρ hirr A f
    refine ⟨q, hq, hardlyTraceTwoAction O hp hdim ρ hρ hirr A f, fun g x ↦
      ⟨he g x, ?_, hardlyTraceTwoAction_sq O hp hdim ρ hρ hirr A f⟩⟩
    intro s hs
    exact hardlyTraceTwoAction_inertia O hp hdim ρ hρ hirr A f s hs

end Deformation
