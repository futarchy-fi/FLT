/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.UniversalLocalQuotient
public import FLT.GaloisRepresentation.Extensions.SurjectiveQuotientFrame
public import FLT.GaloisRepresentation.Extensions.RankOneCharacter
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GaloisRepresentation.HardlyRamified.QuadraticCharacterLift

/-!
# The actual hardly-ramified quotient at two on the global universal ring

The quotient and its quadratic character are extracted from the given
hardly-ramified representation. Its frame is constructed from surjectivity.
The resulting closed quotient of the global universal ring imposes that
specified local sign character. No residual row or local filtration is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GaloisRepresentation GaloisRepresentation.Extensions
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
local notation "k" => residueField (𝓞 := O)
variable {p : ℕ} [Fact p.Prime] (hp : Odd p) [Algebra ℤ_[p] (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V)
  (hρ : IsHardlyRamified hp hdim ρ)

/-- The local quotient functional supplied by the actual HR hypothesis. -/
def hardlyTwoProjection : V →ₗ[k] k := hρ.isTameAtTwo.choose

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Its surjectivity comes from HR, not an added filtration hypothesis. -/
theorem hardlyTwoProjection_surjective : Function.Surjective (hardlyTwoProjection O hp hdim ρ hρ) :=
  hρ.isTameAtTwo.choose_spec.choose

/-- The actual quotient action at two. -/
def hardlyTwoQuotientAction : GaloisRep ℚ_[2] k k :=
  hρ.isTameAtTwo.choose_spec.choose_spec.choose

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The actual local action respects this quotient functional. -/
theorem hardlyTwoProjection_equivariant (g : Field.absoluteGaloisGroup ℚ_[2]) (x : V) :
    hardlyTwoProjection O hp hdim ρ hρ (ρ.map (algebraMap ℚ ℚ_[2]) g x) =
      hardlyTwoQuotientAction O hp hdim ρ hρ g (hardlyTwoProjection O hp hdim ρ hρ x) :=
  (hρ.isTameAtTwo.choose_spec.choose_spec.choose_spec g x).1

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The quotient action is quadratic by the original HR hypothesis. -/
theorem hardlyTwoQuotientAction_sq (g : Field.absoluteGaloisGroup ℚ_[2]) :
    hardlyTwoQuotientAction O hp hdim ρ hρ g * hardlyTwoQuotientAction O hp hdim ρ hρ g = 1 :=
  (hρ.isTameAtTwo.choose_spec.choose_spec.choose_spec 1 0).2.2 g

/-- The residual character of that quotient action. -/
def hardlyTwoCharacter : Field.absoluteGaloisGroup ℚ_[2] →* kˣ :=
  scalarRepresentationCharacter (hardlyTwoQuotientAction O hp hdim ρ hρ).toRepresentation

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The extracted unit character is quadratic. -/
theorem hardlyTwoCharacter_sq (g : Field.absoluteGaloisGroup ℚ_[2]) :
    hardlyTwoCharacter O hp hdim ρ hρ g ^ 2 = 1 :=
  scalarRepresentationCharacter_sq _ (hardlyTwoQuotientAction_sq O hp hdim ρ hρ) g

/-- The global frame is constructed from the actual local quotient at two. -/
def hardlyTwoFrame : (Fin 2 → k) ≃ₗ[k] V :=
  surjectiveQuotientFrame (hardlyTwoProjection O hp hdim ρ hρ)
    (hardlyTwoProjection_surjective O hp hdim ρ hρ) (Module.finrank_eq_of_rank_eq hdim)

/-- The original global representation, in the constructed frame. -/
def hardlyTwoFramedResidual : Field.absoluteGaloisGroup ℚ →ₜ* GL (Fin 2) k :=
  FramedGaloisRep.GL (ρ.conj (hardlyTwoFrame O hp hdim ρ hρ).symm)

/-- The fixed integral sign lift of the actual local quotient. -/
def hardlyTwoIntegralCharacter : Field.absoluteGaloisGroup ℚ_[2] →* Oˣ :=
  quadraticCharacterLift (hardlyTwoCharacter O hp hdim ρ hρ)
    (hardlyTwoCharacter_sq O hp hdim ρ hρ) O

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The fixed integral sign lift is trivial on the original inertia group at two. -/
theorem hardlyTwoIntegralCharacter_unramified (g : Field.absoluteGaloisGroup ℚ_[2])
    (hg : g ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    hardlyTwoIntegralCharacter O hp hdim ρ hρ g = 1 := by
  have he : hardlyTwoQuotientAction O hp hdim ρ hρ g = 1 :=
    (hρ.isTameAtTwo.choose_spec.choose_spec.choose_spec 1 0).2.1 hg
  have hc : hardlyTwoCharacter O hp hdim ρ hρ g = 1 := by
    apply Units.ext
    change hardlyTwoQuotientAction O hp hdim ρ hρ g 1 = 1
    rw [he]
    rfl
  classical
  simp [hardlyTwoIntegralCharacter, quadraticCharacterLift, hc]

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The row equation on the local restriction is proved from HR and the constructed frame. -/
theorem hardlyTwoFramedResidual_row (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    hardlyTwoFramedResidual O hp hdim ρ hρ
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
      if j = 1 then algebraMap O k (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) else 0 := by
  have hred : algebraMap O k (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) =
      (hardlyTwoCharacter O hp hdim ρ hρ g : k) :=
    congrArg Units.val (quadraticCharacterLift_reduce _ _ O (algebraMap O k) g)
  rw [hred]
  change (hardlyTwoFrame O hp hdim ρ hρ).symm
    (ρ.map (algebraMap ℚ ℚ_[2]) g
      (hardlyTwoFrame O hp hdim ρ hρ (Pi.single j 1))) 1 = _
  unfold hardlyTwoFrame
  rw [surjectiveQuotientFrame_symm_one, hardlyTwoProjection_equivariant]
  have hscalar (x : k) : hardlyTwoQuotientAction O hp hdim ρ hρ g x =
      (hardlyTwoCharacter O hp hdim ρ hρ g : k) * x :=
    scalarRepresentationCharacter_apply
      (hardlyTwoQuotientAction O hp hdim ρ hρ).toRepresentation g x
  rw [hscalar]
  change (hardlyTwoCharacter O hp hdim ρ hρ g : k) *
    hardlyTwoProjection O hp hdim ρ hρ
      (quotientFrameMap _ _ _ (Pi.single j 1)) = _
  rw [quotientFrameMap_projection]
  simp [Pi.single_apply, eq_comm]

/-- The global universal deformation ring with its actual HR quotient at two imposed. -/
def hardlyTwoUniversalObject : ProartinianCat O :=
  universalLocalQuotientObject O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ)
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])).toMonoidHom
    (hardlyTwoIntegralCharacter O hp hdim ρ hρ) 1
    (hardlyTwoFramedResidual_row O hp hdim ρ hρ)

/-- Its maps classify global framed lifts with the constructed local sign quotient. -/
def hardlyTwoUniversalEquiv (A : ProartinianCat O) :
    (hardlyTwoUniversalObject O hp hdim ρ hρ ⟶ A) ≃
      {τ : ContinuousFramedLifts O (Field.absoluteGaloisGroup ℚ) (Fin 2)
        (hardlyTwoFramedResidual O hp hdim ρ hρ) A // ∀ g j,
        τ.val (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
          if j = 1 then algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) else 0} :=
  universalLocalQuotientEquiv O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ)
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])).toMonoidHom
    (hardlyTwoIntegralCharacter O hp hdim ρ hρ) 1
    (hardlyTwoFramedResidual_row O hp hdim ρ hρ) A

end Deformation
