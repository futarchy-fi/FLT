/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFreeAdicComplete
public import FLT.GroupScheme.HenselianComponents
public import FLT.GroupScheme.RationalIntegralTransition

/-! # Component lifting over the original rational-place integers -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- The actual special-fibre ideal, without replacing the rational-place base by Z_p. -/
def rationalSpecialIdeal (A : Type*) [CommRing A] [Algebra O A] : Ideal A :=
  (IsLocalRing.maximalIdeal O).map (algebraMap O A)

/-- Finite flat algebras over the original base are complete along their special fibre. -/
theorem rationalFiniteFlat_complete (A : Type*) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] : IsAdicComplete (rationalSpecialIdeal p A) A := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal O) O := rationalCompletionIntegers_adicComplete p
  let : Module.Free O A := Module.free_of_flat_of_isLocalRing
  exact adicComplete_finite_free_algebra (IsLocalRing.maximalIdeal O) A

/-- Henselian lifting is available for every original finite-flat coordinate algebra. -/
theorem rationalFiniteFlat_henselian (A : Type*) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] : HenselianRing A (rationalSpecialIdeal p A) := by
  let := rationalFiniteFlat_complete p A
  infer_instance

/-- The original special fibre is an Artinian finite algebra over the residue field. -/
theorem rationalSpecialFiber_artinian (A : Type*) [CommRing A] [Algebra O A]
    [Module.Finite O A] : IsArtinianRing (A ⧸ rationalSpecialIdeal p A) := by
  let k := IsLocalRing.ResidueField O
  let B := A ⧸ rationalSpecialIdeal p A
  let : Algebra k B := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower O k B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite k B := Module.Finite.of_restrictScalars_finite O k B
  exact IsArtinianRing.of_finite k B

/-- Every original special-fibre idempotent has a unique integral lift. -/
theorem rational_existsUnique_idempotent (A : Type*) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A]
    (e : A ⧸ rationalSpecialIdeal p A) (he : IsIdempotentElem e) :
    ∃! x : A, IsIdempotentElem x ∧ Ideal.Quotient.mk (rationalSpecialIdeal p A) x = e := by
  let := rationalFiniteFlat_henselian p A
  exact existsUnique_idempotent_lift _ e he

end ThreeAdicPlan
