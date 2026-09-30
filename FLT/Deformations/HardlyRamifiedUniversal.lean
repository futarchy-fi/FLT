/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AbsoluteIrreducibility
public import FLT.Deformations.DeSmitLenstra.UniversalTraceLift

/-! # Universal deformation of a residual hardly ramified representation

This constructs the unrestricted universal deformation over the universal trace
ring. It does not assert that this ring has a characteristic-zero point satisfying
the hardly ramified local conditions.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing GaloisRepresentation

namespace Deformation

variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] {p : ℕ} [Fact p.Prime] [Algebra ℤ_[p] O]
  (hpodd : Odd p)

local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "k" => ProartinianCat.residueField (𝓞 := O)

/-- The residual p-adic scalar action is induced through the coefficient ring. -/
local instance residualPadicAlgebra : Algebra ℤ_[p] k :=
  ((IsLocalRing.residue O).comp (algebraMap ℤ_[p] O)).toAlgebra

local instance residualFinite : Finite k :=
  inferInstanceAs (Finite (ResidueField O))

omit [IsNoetherianRing O] [Finite (ResidueField O)] in
/-- Dimension of the residual matrix representation. -/
theorem residual_rank_two : Module.rank k (Fin 2 → k) = 2 := by
  simp

variable (ρ : (repnFunctor (Fin 2) G O).obj .residueField)
  (hirr : (toFramedGaloisRep ρ).IsIrreducible)
  (hρ : IsHardlyRamified hpodd (residual_rank_two O)
    (toFramedGaloisRep ρ))

include hirr hρ

omit [IsNoetherianRing O] in
/-- The matrix representation used by deformation theory is absolutely irreducible
under the existing residual hardly ramified hypotheses. -/
theorem hardlyRamified_residual_absIrred :
    (toRepresentation ρ).IsAbsolutelyIrreducible.{0} := by
  have he : (toFramedGaloisRep ρ).toRepresentation = toRepresentation ρ := by
    ext g x
    rfl
  rw [← he]
  exact IsHardlyRamified.isAbsolutelyIrreducible hpodd _ hρ hirr

/-- The actual universal trace ring carries a universal unrestricted lift,
without assuming absolute irreducibility separately. -/
theorem hardlyRamified_exists_universalTraceLift :
    ∃ σ : (repnFunctor (Fin 2) G O).obj (universalTraceRingObject O G (Fin 2) ρ),
      IsUniversalLift (Fin 2) G O ρ σ := by
  let _abs : (toRepresentation ρ).IsAbsolutelyIrreducible.{0} :=
    hardlyRamified_residual_absIrred O hpodd ρ hirr hρ
  exact MoritaReconstruction.exists_universalTraceLift O G (Fin 2) ρ

/-- The unrestricted deformation functor is corepresentable for the residual
representations occurring in the lifting input. -/
theorem hardlyRamified_isCorepresentable_deformationFunctor :
    (deformationFunctor (Fin 2) G O ρ).toFunctor.IsCorepresentable := by
  obtain ⟨σ, hσ⟩ := hardlyRamified_exists_universalTraceLift O hpodd ρ hirr hρ
  exact (isCorepresentable_deformationFunctor_iff_exists_isUniversalLift
    (Fin 2) G O ρ).mpr ⟨universalTraceRingObject O G (Fin 2) ρ, σ, hσ⟩

end Deformation
