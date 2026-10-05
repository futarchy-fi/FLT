/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceFlat
public import FLT.Deformations.HardlyRamifiedNoetherian
public import FLT.Deformations.PrimeCoefficientOrder

/-!
# Prime orders carrying the actual trace-image representation

Noetherianity makes every prime ideal closed. The corresponding quotient
carries the same residual-compatible representation and its finite-flat
reductions. Finite p-adic coefficients and avoidance of p remain explicit
arithmetic hypotheses; the local quotient at two still needs descent.
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

variable (P : Ideal (hardlyTraceImageObject O hp hdim ρ hρ)) [P.IsPrime]

/-- The prime quotient of the actual trace image, retaining its original residue field. -/
def hardlyTracePrimeObject : ProartinianCat O := by
  let := hardlyTrace_isNoetherianRing O hp hdim ρ hρ hirr
  exact primeCoefficientOrder T P

/-- The canonical continuous map onto this prime quotient. -/
def hardlyTracePrimeProjection : T ⟶ hardlyTracePrimeObject O hp hdim ρ hρ hirr P := by
  let := hardlyTrace_isNoetherianRing O hp hdim ρ hρ hirr
  exact primeCoefficientOrderProjection T P

local notation "D" => hardlyTracePrimeObject O hp hdim ρ hρ hirr P
local notation "f" => hardlyTracePrimeProjection O hp hdim ρ hρ hirr P

/-- Specialization retains the exact original residual frame. -/
def hardlyTracePrimeLift : ContinuousFramedLifts O G (Fin 2) r D := by
  refine ⟨(repnFunctor (Fin 2) G O).map f (hardlyTraceLift O hp hdim ρ hρ hirr).val, ?_⟩
  unfold IsContinuousFramedLift
  ext g i j
  have he : f ≫ toResidueField D = toResidueField T := Subsingleton.elim _ _
  change (f ≫ toResidueField D).hom ((hardlyTraceLift O hp hdim ρ hρ hirr).val g i j) = _
  rw [he]
  exact congrArg (fun t : G →* GL (Fin 2) (residueField (𝓞 := O)) ↦ t g i j)
    (hardlyTraceLift O hp hdim ρ hρ hirr).property

/-- The prime-quotient lift retains the cyclotomic determinant. -/
theorem hardlyTracePrimeLift_det (g : G) :
    ((hardlyTracePrimeLift O hp hdim ρ hρ hirr P).val g).val.det =
      algebraMap O D (hardlyCyclotomicValue (p := p) O g) := by
  change Matrix.det (((hardlyTraceLift O hp hdim ρ hρ hirr).val g).val.map (f).hom) = _
  exact (RingHom.map_det (f).hom.toRingHom _).symm.trans
    ((congrArg (f).hom (hardlyTraceLift_det O hp hdim ρ hρ hirr g)).trans
      ((f).hom.commutes _))

/-- Arithmetic inertia away from 2p remains trivial over the prime quotient. -/
theorem hardlyTracePrimeLift_inertia (g : G) (hg : g ∈ hardlyAwayInertia p) :
    (hardlyTracePrimeLift O hp hdim ρ hρ hirr P).val g = 1 := by
  change Matrix.GeneralLinearGroup.map (f).hom.toRingHom
    ((hardlyTraceLift O hp hdim ρ hρ hirr).val g) = 1
  rw [hardlyTraceLift_inertia O hp hdim ρ hρ hirr g hg, map_one]

/-- Every open reduction of this same prime-quotient lift is finite flat. -/
theorem hardlyTracePrimeLift_isFlat :
    (FramedGaloisRep.ofGL (hardlyTracePrimeLift O hp hdim ρ hρ hirr P).val).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) := by
  change (toFramedGaloisRep ((repnFunctor (Fin 2) G O).map f
    (hardlyTraceLift O hp hdim ρ hρ hirr).val)).IsFlatAt _
  rw [toFramedGaloisRep_map]
  exact hardlyTraceLift_specialization_isFlat O hp hdim ρ hρ hirr D f

/-- The quotient order keeps the original residue field without normalization. -/
def hardlyTracePrimeResidueEquiv :
    IsLocalRing.ResidueField O ≃ₐ[O] IsLocalRing.ResidueField D :=
  IsResidueAlgebra.algEquiv O D

instance hardlyTracePrime_domain : IsDomain D := inferInstanceAs (IsDomain (T ⧸ P))

variable [Algebra ℤ_[p] (hardlyTraceImageObject O hp hdim ρ hρ)]
  [Module.Finite ℤ_[p] (hardlyTraceImageObject O hp hdim ρ hρ)]

instance hardlyTracePrimeAlgebra : Algebra ℤ_[p] D :=
  inferInstanceAs (Algebra ℤ_[p] (T ⧸ P))

instance hardlyTracePrime_finite : Module.Finite ℤ_[p] D :=
  inferInstanceAs (Module.Finite ℤ_[p] (T ⧸ P))

/-- Arithmetic finiteness and avoidance of p give a finite free coefficient domain. -/
theorem hardlyTracePrime_free (hpP : (p : T) ∉ P) : Module.Free ℤ_[p] D := by
  let := hardlyTrace_isNoetherianRing O hp hdim ρ hρ hirr
  exact primeCoefficientOrder_free T P p hpP

/-- The same coefficient domain has characteristic zero. -/
theorem hardlyTracePrime_charZero (hpP : (p : T) ∉ P) : CharZero D := by
  let := hardlyTrace_isNoetherianRing O hp hdim ρ hρ hirr
  exact primeCoefficientOrder_charZero T P p hpP

/-- The representation's quotient topology equals the finite free module topology. -/
theorem hardlyTracePrime_isModuleTopology [ContinuousSMul ℤ_[p] T]
    (hpP : (p : T) ∉ P) : IsModuleTopology ℤ_[p] D := by
  let := hardlyTrace_isNoetherianRing O hp hdim ρ hρ hirr
  exact primeCoefficientOrder_isModuleTopology T P p hpP

end Deformation
