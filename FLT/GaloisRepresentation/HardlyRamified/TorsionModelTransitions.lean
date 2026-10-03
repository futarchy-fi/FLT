/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionGenericTransitions
public import FLT.Deformations.RepresentationTheory.TorsionReductionTower

/-!
# Integral maps of the actual hardly ramified torsion tower

Unique extension turns the original quotient reductions into a coherent
integral tower. The exact-sequence inclusion extends with its prescribed map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)
local notation "v" => LocalCyclotomic.rationalPlace p

include hpodd in
/-- Oddness supplies the numerical extension bound. -/
theorem torsion_prime_gt_two : 2 < p := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ := hpodd
  omega

/-- The integral inclusion extending multiplication on the original quotient. -/
def torsionInclusion (m n : ℕ) :
    ModelHom (hρ.torsionModel m) (hρ.torsionModel (m + n)) :=
  (hρ.torsionGenericInclusion m n).rationalExtension p
    (torsion_prime_gt_two (hpodd := hpodd)) (hρ.torsionModel_killedByPower m)

/-- The integral reduction extending the original quotient map. -/
def torsionReduction (m n : ℕ) :
    ModelHom (hρ.torsionModel (m + n)) (hρ.torsionModel n) :=
  (hρ.torsionGenericReduction m n).rationalExtension p
    (torsion_prime_gt_two (hpodd := hpodd)) (hρ.torsionModel_killedByPower (m + n))

/-- Restriction recovers the original inclusion on generic points. -/
@[simp] theorem genericHom_torsionInclusion (m n : ℕ) :
    genericHom (hρ.torsionInclusion m n) = hρ.torsionGenericInclusion m n :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- Restriction recovers the original reduction on generic points. -/
@[simp] theorem genericHom_torsionReduction (m n : ℕ) :
    genericHom (hρ.torsionReduction m n) = hρ.torsionGenericReduction m n :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- The generic transition between any ordered pair of actual models. -/
def torsionGenericTransition {m n : ℕ} (h : m ≤ n) :
    GenericGaloisHom (hρ.torsionModel n) (hρ.torsionModel m) :=
  hρ.torsionGenericMap (tensorTransition (p : R) h)
    (fun g x ↦ tensorTransition_natural _ _ (ρ.toLocal v g) x)

/-- The integral tower transition with its exact original generic map. -/
def torsionTransition {m n : ℕ} (h : m ≤ n) :
    ModelHom (hρ.torsionModel n) (hρ.torsionModel m) :=
  (hρ.torsionGenericTransition h).rationalExtension p
    (torsion_prime_gt_two (hpodd := hpodd)) (hρ.torsionModel_killedByPower n)

/-- Restriction recovers each prescribed tower transition. -/
@[simp] theorem genericHom_torsionTransition {m n : ℕ} (h : m ≤ n) :
    genericHom (hρ.torsionTransition h) = hρ.torsionGenericTransition h :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- Every reduction triangle commutes on the actual integral models. -/
theorem torsionTransition_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (hρ.torsionTransition k).comp (hρ.torsionTransition h) =
      hρ.torsionTransition (h.trans k) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionTransition]
  apply (hρ.torsionPoints l).injective
  change hρ.torsionPoints l ((hρ.torsionPoints l).symm
    (tensorTransition (p : R) h (hρ.torsionPoints m ((hρ.torsionPoints m).symm
      (tensorTransition (p : R) k (hρ.torsionPoints n x)))))) =
    hρ.torsionPoints l ((hρ.torsionPoints l).symm
      (tensorTransition (p : R) (h.trans k) (hρ.torsionPoints n x)))
  simp only [AddEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (tensorTransition_comp (p : R) h k) _

/-- The tower has identity transition at each integral level. -/
@[simp] theorem torsionTransition_refl (n : ℕ) :
    hρ.torsionTransition (le_refl n) = BialgHom.id _ _ := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionTransition, genericHom_id]
  change (hρ.torsionPoints n).symm
    (tensorTransition (p : R) (le_refl n) (hρ.torsionPoints n x)) = x
  rw [tensorTransition_refl, LinearMap.id_apply, AddEquiv.symm_apply_apply]

end GaloisRepresentation.IsHardlyRamified
