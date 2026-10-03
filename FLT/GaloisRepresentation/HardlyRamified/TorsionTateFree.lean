/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionTateRecovery
public import FLT.GroupScheme.MultiplicativeFiltrationPurity

/-! # Finite freeness of the recovered original Tate module -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  [Module ℤ_[p] V] [IsScalarTower ℤ_[p] R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

include hρ in
omit [IsDomain R] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] R V] in
/-- Every original tensor level is killed by its defining power. -/
theorem torsionTensor_killed (n : ℕ) (x : Level (V := V) (p : R) n) : p ^ n • x = 0 := by
  obtain ⟨x, rfl⟩ := (hρ.torsionPointsUniverses n).surjective x
  exact (map_nsmul (hρ.torsionPointsUniverses n) (p ^ n) x).symm.trans
    ((congrArg (hρ.torsionPointsUniverses n)
      (hρ.torsionModel_killed_universes n x)).trans (map_zero _))

/-- The canonical finite-level action on the original chosen point groups. -/
local instance instModulePadicTorsionPoints (n : ℕ) :
    Module ℤ_[p] (hρ.torsionModelUniverses n).Points :=
  PDivisibleSystem.instModulePadicPoints hρ.torsionPDivisibleUniverses n

omit [Module ℤ_[p] V] [IsScalarTower ℤ_[p] R V] in
/-- The chosen additive point comparisons preserve the canonical p-adic scalars. -/
theorem torsionPoints_padic_smul (n : ℕ) (a : ℤ_[p])
    (x : (hρ.torsionPDivisibleUniverses.level n).Points) :
    hρ.torsionPointsUniverses n (a • x) =
      a • (show Level (V := V) (p : R) n from hρ.torsionPointsUniverses n x) := by
  rw [padic_smul_eq_nsmul_of_pow_kills p n (hρ.torsionModel_killed_universes n),
    padic_smul_eq_nsmul_of_pow_kills p n (hρ.torsionTensor_killed n), map_nsmul]

/-- The recovery equivalence is linear for the previously constructed p-adic Tate action. -/
def torsionTateRecoveryLinear : V ≃ₗ[ℤ_[p]] hρ.torsionPDivisibleUniverses.tateSequences where
  __ := hρ.torsionTateRecovery
  map_smul' a x := by
    apply hρ.torsionPDivisibleUniverses.tate_ext
    intro n
    apply (hρ.torsionPointsUniverses n).injective
    change hρ.torsionPointsUniverses n
      (hρ.torsionPDivisibleUniverses.tateEval n (hρ.torsionTateRecovery (a • x))) =
      hρ.torsionPointsUniverses n (a •
        hρ.torsionPDivisibleUniverses.tateEval n (hρ.torsionTateRecovery x))
    rw [hρ.torsionPoints_padic_smul, hρ.torsionTateRecovery_eval,
      hρ.torsionTateRecovery_eval]
    exact TensorProduct.tmul_smul _ _ _

/-- The actual Tate module is finite over the p-adic integers. -/
theorem torsionTate_finite : Module.Finite ℤ_[p] hρ.torsionPDivisibleUniverses.tateSequences := by
  let := Module.Finite.trans R V (R := ℤ_[p])
  exact Module.Finite.of_surjective hρ.torsionTateRecoveryLinear.toLinearMap
    hρ.torsionTateRecoveryLinear.surjective

/-- The actual Tate module is free over the p-adic integers. -/
theorem torsionTate_free : Module.Free ℤ_[p] hρ.torsionPDivisibleUniverses.tateSequences := by
  let : Module.Free ℤ_[p] V := Module.Free.trans (R := ℤ_[p]) (S := R) (M := V)
  exact Module.Free.of_equiv hρ.torsionTateRecoveryLinear

/-- Recovery retains the full p-adic rank of the original lattice. -/
theorem torsionTate_finrank : Module.finrank ℤ_[p] hρ.torsionPDivisibleUniverses.tateSequences =
    Module.finrank ℤ_[p] V := hρ.torsionTateRecoveryLinear.finrank_eq.symm

/-- The Tate rank is twice the original coefficient degree. -/
theorem torsionTate_finrank_eq_height :
    Module.finrank ℤ_[p] hρ.torsionPDivisibleUniverses.tateSequences =
      Module.finrank ℤ_[p] R * 2 := by
  rw [hρ.torsionTate_finrank, ← Module.finrank_mul_finrank ℤ_[p] R V]
  have hd : Module.finrank R V = 2 := by
    simp [Module.finrank, hV]
  rw [hd]

end GaloisRepresentation.IsHardlyRamified
