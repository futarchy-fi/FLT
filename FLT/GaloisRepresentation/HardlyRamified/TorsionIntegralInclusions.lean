/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionModelTransitions
public import FLT.Deformations.RepresentationTheory.TorsionInclusionTower

/-!
# Inclusion and multiplication diagrams of the integral torsion tower

The original tensor inclusions extend coherently, and their composites with
reduction are the actual integral group-scheme multiplication maps.
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

/-- The generic inclusion between arbitrary ordered levels. -/
def torsionGenericEmbedding {m n : ℕ} (h : m ≤ n) :
    GenericGaloisHom (hρ.torsionModel m) (hρ.torsionModel n) :=
  hρ.torsionGenericMap (tensorEmbedding (p : R) h)
    (fun g x ↦ tensorEmbedding_natural _ _ (ρ.toLocal v g) x)

/-- The integral inclusion extending the original p^(n-m) map. -/
def torsionEmbedding {m n : ℕ} (h : m ≤ n) :
    ModelHom (hρ.torsionModel m) (hρ.torsionModel n) :=
  (hρ.torsionGenericEmbedding h).rationalExtension p
    (torsion_prime_gt_two (hpodd := hpodd)) (hρ.torsionModel_killedByPower m)

/-- Restriction recovers the original inclusion. -/
@[simp] theorem genericHom_torsionEmbedding {m n : ℕ} (h : m ≤ n) :
    genericHom (hρ.torsionEmbedding h) = hρ.torsionGenericEmbedding h :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- The original point comparison intertwines inclusion. -/
@[simp] theorem torsionPoints_embedding {m n : ℕ} (h : m ≤ n)
    (x : (hρ.torsionModel m).Points) :
    hρ.torsionPoints n (hρ.torsionGenericEmbedding h x) =
      tensorEmbedding (p : R) h (hρ.torsionPoints m x) :=
  (hρ.torsionPoints n).apply_symm_apply _

/-- The original point comparison intertwines every reduction. -/
@[simp] theorem torsionPoints_transition {m n : ℕ} (h : m ≤ n)
    (x : (hρ.torsionModel n).Points) :
    hρ.torsionPoints m (hρ.torsionGenericTransition h x) =
      tensorTransition (p : R) h (hρ.torsionPoints n x) :=
  (hρ.torsionPoints m).apply_symm_apply _

/-- Inclusion triangles commute on the prescribed integral models. -/
theorem torsionEmbedding_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (hρ.torsionEmbedding h).comp (hρ.torsionEmbedding k) =
      hρ.torsionEmbedding (h.trans k) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionEmbedding]
  apply (hρ.torsionPoints n).injective
  simp only [torsionPoints_embedding]
  exact DFunLike.congr_fun (tensorEmbedding_comp (p : R) h k) _

/-- Inclusion then reduction is actual multiplication on the lower integral level. -/
theorem torsionEmbedding_comp_transition {m n : ℕ} (h : m ≤ n) :
    (hρ.torsionEmbedding h).comp (hρ.torsionTransition h) =
      (hρ.torsionModel m).multiply (p ^ (n - m)) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionEmbedding, genericHom_torsionTransition,
    FF.genericHom_multiply]
  apply (hρ.torsionPoints m).injective
  rw [map_nsmul, torsionPoints_transition, torsionPoints_embedding]
  let y : Level (V := V) (p : R) m := hρ.torsionPoints m x
  have he := DFunLike.congr_fun (tensorTransition_embedding (V := V) (p : R) h) y
  change tensorTransition (p : R) h (tensorEmbedding (p : R) h y) = (p : R) ^ (n - m) • y at he
  exact he.trans ((congrArg (fun r : R ↦ r • y) (Nat.cast_pow p (n - m)).symm).trans
    (Nat.cast_smul_eq_nsmul R (p ^ (n - m)) y))

/-- Reduction then inclusion is actual multiplication on the higher integral level. -/
theorem torsionTransition_comp_embedding {m n : ℕ} (h : m ≤ n) :
    (hρ.torsionTransition h).comp (hρ.torsionEmbedding h) =
      (hρ.torsionModel n).multiply (p ^ (n - m)) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionEmbedding, genericHom_torsionTransition,
    FF.genericHom_multiply]
  apply (hρ.torsionPoints n).injective
  rw [map_nsmul, torsionPoints_embedding, torsionPoints_transition]
  let y : Level (V := V) (p : R) n := hρ.torsionPoints n x
  have he := DFunLike.congr_fun (tensorEmbedding_transition (V := V) (p : R) h) y
  change tensorEmbedding (p : R) h (tensorTransition (p : R) h y) = (p : R) ^ (n - m) • y at he
  exact he.trans ((congrArg (fun r : R ↦ r • y) (Nat.cast_pow p (n - m)).symm).trans
    (Nat.cast_smul_eq_nsmul R (p ^ (n - m)) y))

/-- The coherent inclusion is the same map used in the integral exact sequence. -/
theorem torsionEmbedding_eq_inclusion (m n : ℕ) :
    hρ.torsionEmbedding (Nat.le_add_right m n) = hρ.torsionInclusion m n := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionEmbedding, genericHom_torsionInclusion]
  apply (hρ.torsionPoints (m + n)).injective
  rw [torsionPoints_embedding, torsionPoints_inclusion]
  exact DFunLike.congr_fun (tensorEmbedding_eq_inclusion (p : R) m n) _

/-- The coherent reduction is the same map used in the integral exact sequence. -/
theorem torsionTransition_eq_reduction (m n : ℕ) :
    hρ.torsionTransition (Nat.le_add_left n m) = hρ.torsionReduction m n := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionTransition, genericHom_torsionReduction]
  apply (hρ.torsionPoints n).injective
  rw [torsionPoints_transition, torsionPoints_reduction]
  exact DFunLike.congr_fun (tensorTransition_eq_reduction (p : R) m n) _

/-- Inclusion at the same integral level is the identity. -/
@[simp] theorem torsionEmbedding_refl (n : ℕ) :
    hρ.torsionEmbedding (le_refl n) = BialgHom.id _ _ := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionEmbedding, genericHom_id]
  apply (hρ.torsionPoints n).injective
  rw [torsionPoints_embedding, tensorEmbedding_refl, LinearMap.id_apply]

end GaloisRepresentation.IsHardlyRamified
