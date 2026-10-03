/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionFlatModels
public import FLT.GroupScheme.RationalIntegralTransition

/-!
# Chosen models and their original torsion point comparisons

All models and equivariant comparisons are chosen from hardly ramifiedness.
The models live over the rational completion used by the extension theorem.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

include hρ in
/-- Existence with the exact rational-place convention of integral extension. -/
theorem exists_rational_torsion_model (n : ℕ) :
    ∃ (X : FF O K)
      (e : X.Points ≃+ ((ρ.baseChange (R ⧸ Ideal.span {(p : R) ^ n})).toLocal v).Space),
      (∀ (g : Field.absoluteGaloisGroup K) (x : X.Points), e (g • x) = g • e x) ∧
        ∀ x : X.Points, p ^ n • x = 0 := by
  rw [rationalPlace_eq_primePlace]
  exact exists_torsion_flat_model hpodd hV hρ n

/-- The chosen actual integral model of the nth torsion reduction. -/
def torsionModel (n : ℕ) : FF O K := (hρ.exists_rational_torsion_model n).choose

/-- The chosen comparison retains the original quotient tensor module. -/
def torsionPoints (n : ℕ) :
    (hρ.torsionModel n).Points ≃+
      ((ρ.baseChange (R ⧸ Ideal.span {(p : R) ^ n})).toLocal v).Space :=
  (hρ.exists_rational_torsion_model n).choose_spec.choose

/-- The comparison respects the original local Galois action. -/
theorem torsionPoints_smul (n : ℕ) (g : Field.absoluteGaloisGroup K)
    (x : (hρ.torsionModel n).Points) :
    hρ.torsionPoints n (g • x) = g • hρ.torsionPoints n x :=
  (hρ.exists_rational_torsion_model n).choose_spec.choose_spec.1 g x

/-- The model is killed by the same power as the original reduction. -/
theorem torsionModel_killed (n : ℕ) (x : (hρ.torsionModel n).Points) : p ^ n • x = 0 :=
  (hρ.exists_rational_torsion_model n).choose_spec.choose_spec.2 x

/-- Every chosen level satisfies the extension theorem's annihilation condition. -/
theorem torsionModel_killedByPower (n : ℕ) : KilledByPowerOf p (hρ.torsionModel n) :=
  ⟨n, hρ.torsionModel_killed n⟩

end GaloisRepresentation.IsHardlyRamified
