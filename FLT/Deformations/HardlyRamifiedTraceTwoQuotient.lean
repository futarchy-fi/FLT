/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTraceTwoRow
public import FLT.Deformations.HardlyRamifiedTraceOrder

/-!
# The same quotient at two on trace coefficients and prime orders

The descended normalized row gives a surjective linear functional with the
specified integral sign character. Coefficient specialization preserves its
residual row and equivariance, including on every prime coefficient quotient.
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

/-- The constructed normalized parameter of the local quotient at two. -/
def hardlyTraceTwoParameter : T := (exists_hardlyTraceTwoRow O hp hdim ρ hρ hirr).choose

/-- The parameter vanishes in the original residue field. -/
theorem hardlyTraceTwoParameter_residue :
    (toResidueField T).hom (hardlyTraceTwoParameter O hp hdim ρ hρ hirr) = 0 :=
  (exists_hardlyTraceTwoRow O hp hdim ρ hρ hirr).choose_spec.1

/-- The constructed parameter satisfies every local row equation. -/
theorem hardlyTraceTwoParameter_row (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    hardlyTraceTwoParameter O hp hdim ρ hρ hirr *
      (hardlyTraceLift O hp hdim ρ hρ hirr).val
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 0 j +
      (hardlyTraceLift O hp hdim ρ hρ hirr).val
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
      algebraMap O T (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) *
        (if j = 0 then hardlyTraceTwoParameter O hp hdim ρ hρ hirr else 1) :=
  (exists_hardlyTraceTwoRow O hp hdim ρ hρ hirr).choose_spec.2.2 g j

variable (A : ProartinianCat O) (f : hardlyTraceImageObject O hp hdim ρ hρ ⟶ A)

/-- The specified quotient functional after any coefficient specialization. -/
def hardlyTraceTwoQuotient : (Fin 2 → A) →ₗ[A] A :=
  normalizedQuotient (f.hom (hardlyTraceTwoParameter O hp hdim ρ hρ hirr))

/-- Its section is the original second coordinate. -/
theorem hardlyTraceTwoQuotient_surjective :
    Function.Surjective (hardlyTraceTwoQuotient O hp hdim ρ hρ hirr A f) :=
  normalizedQuotient_surjective _

/-- Reduction recovers the original quotient row, not a new residual quotient. -/
theorem hardlyTraceTwoQuotient_residue (x : Fin 2 → A) :
    (toResidueField A).hom (hardlyTraceTwoQuotient O hp hdim ρ hρ hirr A f x) =
      (toResidueField A).hom (x 1) := by
  have hf : f ≫ toResidueField A = toResidueField T := Subsingleton.elim _ _
  have ht : (toResidueField A).hom (f.hom (hardlyTraceTwoParameter O hp hdim ρ hρ hirr)) =
      0 := by
    change (f ≫ toResidueField A).hom _ = _
    rw [hf, hardlyTraceTwoParameter_residue]
  change (toResidueField A).hom (_ * x 0 + x 1) = _
  rw [map_add, map_mul, ht, zero_mul, zero_add]

/-- The actual specialized representation acts through the fixed integral sign character. -/
theorem hardlyTraceTwoQuotient_equivariant (g : Field.absoluteGaloisGroup ℚ_[2])
    (x : Fin 2 → A) :
    hardlyTraceTwoQuotient O hp hdim ρ hρ hirr A f
      ((toFramedGaloisRep ((repnFunctor (Fin 2) G O).map f
        (hardlyTraceLift O hp hdim ρ hρ hirr).val)).map (algebraMap ℚ ℚ_[2]) g x) =
      algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) *
        hardlyTraceTwoQuotient O hp hdim ρ hρ hirr A f x := by
  apply normalizedQuotient_equivariant
  intro j
  have he := congrArg f.hom (hardlyTraceTwoParameter_row O hp hdim ρ hρ hirr g j)
  simp only [map_add, map_mul] at he
  erw [f.hom.commutes] at he
  fin_cases j <;> simpa using he

/-- In particular the prime coefficient order carries the same specified quotient. -/
theorem hardlyTracePrimeLift_twoQuotient
    (P : Ideal (hardlyTraceImageObject O hp hdim ρ hρ)) [P.IsPrime] :
    ∃ q : (Fin 2 → hardlyTracePrimeObject O hp hdim ρ hρ hirr P) →ₗ[
        hardlyTracePrimeObject O hp hdim ρ hρ hirr P]
        hardlyTracePrimeObject O hp hdim ρ hρ hirr P,
      Function.Surjective q ∧ ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) x,
        q ((FramedGaloisRep.ofGL (hardlyTracePrimeLift O hp hdim ρ hρ hirr P).val).map
          (algebraMap ℚ ℚ_[2]) g x) =
        algebraMap O (hardlyTracePrimeObject O hp hdim ρ hρ hirr P)
          (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) * q x :=
  ⟨hardlyTraceTwoQuotient O hp hdim ρ hρ hirr _
      (hardlyTracePrimeProjection O hp hdim ρ hρ hirr P),
    hardlyTraceTwoQuotient_surjective O hp hdim ρ hρ hirr _ _,
    hardlyTraceTwoQuotient_equivariant O hp hdim ρ hρ hirr _ _⟩

end Deformation
