/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionTransitionsUniverses
public import FLT.Deformations.RepresentationTheory.TorsionInclusionTower

/-!
# Arbitrary-universe Inclusion and multiplication diagrams of the integral torsion tower

The original tensor inclusions extend coherently, and their composites with
reduction are the actual integral group-scheme multiplication maps.
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

/-- The generic inclusion between arbitrary ordered levels. -/
def torsionGenericEmbeddingUniverses {m n : ℕ} (h : m ≤ n) :
    GenericGaloisHom (hρ.torsionModelUniverses m) (hρ.torsionModelUniverses n) :=
  hρ.torsionGenericMapUniverses (tensorEmbedding (p : R) h)
    (fun g x ↦ tensorEmbedding_natural _ _ (ρ.toLocal v g) x)

/-- The integral inclusion extending the original p^(n-m) map. -/
def torsionEmbeddingUniverses {m n : ℕ} (h : m ≤ n) :
    ModelHom (hρ.torsionModelUniverses m) (hρ.torsionModelUniverses n) :=
  (hρ.torsionGenericEmbeddingUniverses h).rationalExtension p
    (torsion_prime_gt_two_universes (hpodd := hpodd)) (hρ.torsionModel_killedByPower_universes m)

/-- Restriction recovers the original inclusion. -/
@[simp] theorem genericHom_torsionEmbeddingUniverses {m n : ℕ} (h : m ≤ n) :
    genericHom (hρ.torsionEmbeddingUniverses h) = hρ.torsionGenericEmbeddingUniverses h :=
  GenericGaloisHom.genericHom_rationalExtension ..

/-- The original point comparison intertwines inclusion. -/
@[simp] theorem torsionPoints_embedding_universes {m n : ℕ} (h : m ≤ n)
    (x : (hρ.torsionModelUniverses m).Points) :
    hρ.torsionPointsUniverses n (hρ.torsionGenericEmbeddingUniverses h x) =
      tensorEmbedding (p : R) h (hρ.torsionPointsUniverses m x) :=
  (hρ.torsionPointsUniverses n).apply_symm_apply _

/-- The original point comparison intertwines every reduction. -/
@[simp] theorem torsionPoints_transition_universes {m n : ℕ} (h : m ≤ n)
    (x : (hρ.torsionModelUniverses n).Points) :
    hρ.torsionPointsUniverses m (hρ.torsionGenericTransitionUniverses h x) =
      tensorTransition (p : R) h (hρ.torsionPointsUniverses n x) :=
  (hρ.torsionPointsUniverses m).apply_symm_apply _

/-- Inclusion triangles commute on the prescribed integral models. -/
theorem torsionEmbedding_comp_universes {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (hρ.torsionEmbeddingUniverses h).comp (hρ.torsionEmbeddingUniverses k) =
      hρ.torsionEmbeddingUniverses (h.trans k) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionEmbeddingUniverses]
  apply (hρ.torsionPointsUniverses n).injective
  simp only [torsionPoints_embedding_universes]
  exact DFunLike.congr_fun (tensorEmbedding_comp (p : R) h k) _

/-- Inclusion then reduction is actual multiplication on the lower integral level. -/
theorem torsionEmbedding_comp_transition_universes {m n : ℕ} (h : m ≤ n) :
    (hρ.torsionEmbeddingUniverses h).comp (hρ.torsionTransitionUniverses h) =
      (hρ.torsionModelUniverses m).multiply (p ^ (n - m)) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionEmbeddingUniverses,
    genericHom_torsionTransitionUniverses,
    FF.genericHom_multiply]
  apply (hρ.torsionPointsUniverses m).injective
  rw [map_nsmul, torsionPoints_transition_universes, torsionPoints_embedding_universes]
  let y : Level (V := V) (p : R) m := hρ.torsionPointsUniverses m x
  have he := DFunLike.congr_fun (tensorTransition_embedding (V := V) (p : R) h) y
  change tensorTransition (p : R) h (tensorEmbedding (p : R) h y) = (p : R) ^ (n - m) • y at he
  exact he.trans ((congrArg (fun r : R ↦ r • y) (Nat.cast_pow p (n - m)).symm).trans
    (Nat.cast_smul_eq_nsmul R (p ^ (n - m)) y))

/-- Reduction then inclusion is actual multiplication on the higher integral level. -/
theorem torsionTransition_comp_embedding_universes {m n : ℕ} (h : m ≤ n) :
    (hρ.torsionTransitionUniverses h).comp (hρ.torsionEmbeddingUniverses h) =
      (hρ.torsionModelUniverses n).multiply (p ^ (n - m)) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, genericHom_torsionEmbeddingUniverses,
    genericHom_torsionTransitionUniverses,
    FF.genericHom_multiply]
  apply (hρ.torsionPointsUniverses n).injective
  rw [map_nsmul, torsionPoints_embedding_universes, torsionPoints_transition_universes]
  let y : Level (V := V) (p : R) n := hρ.torsionPointsUniverses n x
  have he := DFunLike.congr_fun (tensorEmbedding_transition (V := V) (p : R) h) y
  change tensorEmbedding (p : R) h (tensorTransition (p : R) h y) = (p : R) ^ (n - m) • y at he
  exact he.trans ((congrArg (fun r : R ↦ r • y) (Nat.cast_pow p (n - m)).symm).trans
    (Nat.cast_smul_eq_nsmul R (p ^ (n - m)) y))

/-- The coherent inclusion is the same map used in the integral exact sequence. -/
theorem torsionEmbedding_eq_inclusion_universes (m n : ℕ) :
    hρ.torsionEmbeddingUniverses (Nat.le_add_right m n) = hρ.torsionInclusionUniverses m n := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionEmbeddingUniverses, genericHom_torsionInclusionUniverses]
  apply (hρ.torsionPointsUniverses (m + n)).injective
  rw [torsionPoints_embedding_universes, torsionPoints_inclusion_universes]
  exact DFunLike.congr_fun (tensorEmbedding_eq_inclusion (p : R) m n) _

/-- The coherent reduction is the same map used in the integral exact sequence. -/
theorem torsionTransition_eq_reduction_universes (m n : ℕ) :
    hρ.torsionTransitionUniverses (Nat.le_add_left n m) = hρ.torsionReductionUniverses m n := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionTransitionUniverses, genericHom_torsionReductionUniverses]
  apply (hρ.torsionPointsUniverses n).injective
  rw [torsionPoints_transition_universes, torsionPoints_reduction_universes]
  exact DFunLike.congr_fun (tensorTransition_eq_reduction (p : R) m n) _

/-- Inclusion at the same integral level is the identity. -/
@[simp] theorem torsionEmbedding_refl_universes (n : ℕ) :
    hρ.torsionEmbeddingUniverses (le_refl n) = BialgHom.id _ _ := by
  apply genericHom_injective
  ext x
  simp only [genericHom_torsionEmbeddingUniverses, genericHom_id]
  apply (hρ.torsionPointsUniverses n).injective
  rw [torsionPoints_embedding_universes, tensorEmbedding_refl, LinearMap.id_apply]

end GaloisRepresentation.IsHardlyRamified
