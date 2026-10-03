/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionPDivisibleUniverses
public import FLT.GroupScheme.TateProjectionSurjective

/-! # Surjective evaluations for the original hardly ramified Tate tower -/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

omit [IsDomain R] in
/-- Every prescribed reduction of the original geometric point groups is onto. -/
theorem torsionTransition_points_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (genericHom (hρ.torsionTransitionUniverses h)) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have hn : n = d + m := hd.trans (Nat.add_comm m d)
  clear hd
  subst n
  rw [hρ.torsionTransition_eq_reduction_universes,
    hρ.genericHom_torsionReductionUniverses]
  exact hρ.torsionGenericReduction_surjective_universes d m

/-- Every original torsion point is the evaluation of an actual coherent Tate sequence. -/
theorem torsionTate_eval_surjective (n : ℕ) :
    Function.Surjective (hρ.torsionPDivisibleUniverses.tateEval n) :=
  hρ.torsionPDivisibleUniverses.tateEval_surjective
    (fun h ↦ hρ.torsionTransition_points_surjective h) n

end GaloisRepresentation.IsHardlyRamified
