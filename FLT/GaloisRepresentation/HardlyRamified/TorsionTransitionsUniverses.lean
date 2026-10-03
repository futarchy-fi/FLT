/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionGenericUniverses
public import FLT.Deformations.RepresentationTheory.TorsionReductionTower

/-!
# Arbitrary-universe Integral maps of the actual hardly ramified torsion tower

Unique extension turns the original quotient reductions into a coherent
integral tower. The exact-sequence inclusion extends with its prescribed map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type*} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)
local notation "v" => LocalCyclotomic.rationalPlace p

include hpodd in
/-- Oddness supplies the numerical extension bound. -/
theorem torsion_prime_gt_two_universes : 2 < p := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ := hpodd
  omega

/-- The integral inclusion extending multiplication on the original quotient. -/
def torsionInclusionUniverses (m n : ℕ) :
    ModelHom (hρ.torsionModelUniverses m) (hρ.torsionModelUniverses (m + n)) :=
  (hρ.torsionGenericInclusionUniverses m n).rationalExtension p
    (torsion_prime_gt_two_universes (hpodd := hpodd)) (hρ.torsionModel_killedByPower_universes m)

/-- The integral reduction extending the original quotient map. -/
def torsionReductionUniverses (m n : ℕ) :
    ModelHom (hρ.torsionModelUniverses (m + n)) (hρ.torsionModelUniverses n) :=
  (hρ.torsionGenericReductionUniverses m n).rationalExtension p
    (torsion_prime_gt_two_universes (hpodd :=
      hpodd)) (hρ.torsionModel_killedByPower_universes (m + n))

/-- Restriction recovers the original inclusion on generic points. -/
@[simp] theorem genericHom_torsionInclusionUniverses (m n : ℕ) :
    genericHom (hρ.torsionInclusionUniverses m n) = hρ.torsionGenericInclusionUniverses m n :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- Restriction recovers the original reduction on generic points. -/
@[simp] theorem genericHom_torsionReductionUniverses (m n : ℕ) :
    genericHom (hρ.torsionReductionUniverses m n) = hρ.torsionGenericReductionUniverses m n :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- The generic transition between any ordered pair of actual models. -/
def torsionGenericTransitionUniverses {m n : ℕ} (h : m ≤ n) :
    GenericGaloisHom (hρ.torsionModelUniverses n) (hρ.torsionModelUniverses m) :=
  hρ.torsionGenericMapUniverses (tensorTransition (p : R) h)
    (fun g x ↦ tensorTransition_natural _ _ (ρ.toLocal v g) x)

/-- The integral tower transition with its exact original generic map. -/
def torsionTransitionUniverses {m n : ℕ} (h : m ≤ n) :
    ModelHom (hρ.torsionModelUniverses n) (hρ.torsionModelUniverses m) :=
  (hρ.torsionGenericTransitionUniverses h).rationalExtension p
    (torsion_prime_gt_two_universes (hpodd := hpodd)) (hρ.torsionModel_killedByPower_universes n)

/-- Restriction recovers each prescribed tower transition. -/
@[simp] theorem genericHom_torsionTransitionUniverses {m n : ℕ} (h : m ≤ n) :
    genericHom (hρ.torsionTransitionUniverses h) = hρ.torsionGenericTransitionUniverses h :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- Every reduction triangle commutes on the actual integral models. -/
theorem torsionTransition_comp_universes {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (hρ.torsionTransitionUniverses k).comp (hρ.torsionTransitionUniverses h) =
      hρ.torsionTransitionUniverses (h.trans k) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionTransitionUniverses]
  apply (hρ.torsionPointsUniverses l).injective
  change hρ.torsionPointsUniverses l ((hρ.torsionPointsUniverses l).symm
    (tensorTransition (p : R) h (hρ.torsionPointsUniverses m ((hρ.torsionPointsUniverses m).symm
      (tensorTransition (p : R) k (hρ.torsionPointsUniverses n x)))))) =
    hρ.torsionPointsUniverses l ((hρ.torsionPointsUniverses l).symm
      (tensorTransition (p : R) (h.trans k) (hρ.torsionPointsUniverses n x)))
  simp only [AddEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (tensorTransition_comp (p : R) h k) _

/-- The tower has identity transition at each integral level. -/
@[simp] theorem torsionTransition_refl_universes (n : ℕ) :
    hρ.torsionTransitionUniverses (le_refl n) = BialgHom.id _ _ := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionTransitionUniverses, genericHom_id]
  change (hρ.torsionPointsUniverses n).symm
    (tensorTransition (p : R) (le_refl n) (hρ.torsionPointsUniverses n x)) = x
  rw [tensorTransition_refl, LinearMap.id_apply, AddEquiv.symm_apply_apply]

end GaloisRepresentation.IsHardlyRamified
