/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Slop.Ribet_Lemma.stable_lattices

/-!
# Continuous representations on stable lattices

For a topological DVR `O` with fraction field `K`, a stable lattice inherits a
continuous representation when the topology on `O` is induced from `K`.
Continuity is proved for the module topology on its endomorphism ring.
-/

@[expose] public section

open Module IsLocalRing
open scoped TensorProduct Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

variable {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Coordinates of lattice vectors agree with the coordinates in the extended basis. -/
theorem lattice_basis_repr {Λ : Submodule O W} [Submodule.IsLattice K Λ]
    {ι : Type*} (b : Basis ι O Λ) (x : Λ) (i : ι) :
    (b.extendOfIsLattice K).repr (x : W) i = algebraMap O K (b.repr x i) := by
  classical
  let f : Λ →ₗ[O] K :=
    (((b.extendOfIsLattice K).coord i).restrictScalars O).comp Λ.subtype
  let f' : Λ →ₗ[O] K := (Algebra.linearMap O K).comp (b.coord i)
  have hf : f = f' := b.ext fun j => by
    change (b.extendOfIsLattice K).repr (b j : W) i = algebraMap O K (b.repr (b j) i)
    rw [← Basis.extendOfIsLattice_apply K b j]
    simp only [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun hf x

variable [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- Restriction to a stable lattice is continuous for the module topology. -/
theorem continuous_latticeRep (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) :
    Continuous[_, moduleTopology O (Module.End O Λ)]
      (StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable) := by
  classical
  let := hΛ.isLattice
  let := moduleTopology O (Module.End O Λ)
  let := moduleTopology K (Module.End K W)
  let b := Module.Free.chooseBasis O Λ
  let c := b.extendOfIsLattice K
  let e : Module.End O Λ ≃A[O] Matrix _ _ O :=
    .ofIsModuleTopology (LinearMap.toMatrixAlgEquiv b)
  let eK : Module.End K W ≃A[K] Matrix _ _ K :=
    .ofIsModuleTopology (LinearMap.toMatrixAlgEquiv c)
  apply e.toHomeomorph.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply hOK.continuous_iff.mpr
  have heq : (fun g => algebraMap O K
      (e (StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable g) i j)) =
      (fun g => eK (ρK g) i j) := by
    funext g
    change algebraMap O K
      (LinearMap.toMatrixAlgEquiv b
        (StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable g) i j) =
      LinearMap.toMatrixAlgEquiv c (ρK g) i j
    simp only [LinearMap.toMatrixAlgEquiv_apply]
    rw [← lattice_basis_repr b]
    simp [c, StableLattice.latticeRep_apply_coe, GaloisRep.toRepresentation]
  change Continuous (fun g => algebraMap O K
    (e (StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable g) i j))
  rw [heq]
  exact (continuous_apply j).comp ((continuous_apply i).comp (eK.continuous.comp ρK.continuous))

/-- The continuous `O`-linear representation on a stable lattice. -/
def latticeGaloisRep (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) : GaloisRep ℚ O Λ :=
  letI := moduleTopology O (Module.End O Λ)
  { toMonoidHom := StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable
    continuous_toFun := continuous_latticeRep ρK Λ hΛ hOK }

/-- Forgetting continuity gives the existing algebraic lattice representation. -/
@[simp]
theorem latticeGaloisRep_toRepresentation (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) :
    (latticeGaloisRep ρK Λ hΛ hOK).toRepresentation =
      StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable := rfl

/-- Tensoring the lattice with the residue field gives its algebraic reduction,
compatibly with the Galois action. -/
theorem lattice_residue_equiv
    [TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]
    [ContinuousSMul O (ResidueField O)] (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) :
    let := hΛ.isLattice
    ∃ e : (ResidueField O ⊗[O] Λ) ≃ₗ[ResidueField O] StableLattice.Reduction O W Λ,
      ∀ g x, e (((latticeGaloisRep ρK Λ hΛ hOK).baseChange (ResidueField O)) g x) =
        StableLattice.reducedRep ρK.toRepresentation Λ hΛ.stable g (e x) := by
  let := hΛ.isLattice
  let e : (ResidueField O ⊗[O] Λ) ≃ₗ[ResidueField O] StableLattice.Reduction O W Λ :=
    (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal O)).extendScalarsOfSurjective
      (IsLocalRing.residue_surjective (R := O))
  refine ⟨e, ?_⟩
  intro g x
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal O)
        (Ideal.Quotient.mk (maximalIdeal O) a ⊗ₜ[O]
          StableLattice.latticeRep ρK.toRepresentation Λ hΛ.stable g x) =
      StableLattice.reducedRep ρK.toRepresentation Λ hΛ.stable g
        (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal O)
          (Ideal.Quotient.mk (maximalIdeal O) a ⊗ₜ[O] x))
    simp only [TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
      StableLattice.reducedRep_mk, map_smul]
  | add x y hx hy => simp [hx, hy]

/-- Extending scalars back to the fraction field recovers the original
continuous representation. -/
theorem lattice_generic_equiv (ρK : GaloisRep ℚ K W) (Λ : Submodule O W)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) :
    letI := hΛ.isLattice
    letI : ContinuousSMul O K := continuousSMul_of_algebraMap O K hOK.continuous
    ∃ e : (K ⊗[O] Λ) ≃ₗ[K] W,
      ((latticeGaloisRep ρK Λ hΛ hOK).baseChange K).conj e = ρK := by
  classical
  let := hΛ.isLattice
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K hOK.continuous
  let b := Module.Free.chooseBasis O Λ
  let e : (K ⊗[O] Λ) ≃ₗ[K] W :=
    (b.baseChange K).equiv (b.extendOfIsLattice K) (Equiv.refl _)
  have he : e.toLinearMap = Λ.subtype.liftBaseChange K := by
    apply (b.baseChange K).ext
    intro i
    change (b.baseChange K).equiv (b.extendOfIsLattice K) (Equiv.refl _)
      ((b.baseChange K) i) = _
    rw [Basis.equiv_apply]
    simp
  have het (r : K) (x : Λ) : e (r ⊗ₜ[O] x) = r • (x : W) := by
    change e.toLinearMap (r ⊗ₜ[O] x) = _
    rw [he]
    rfl
  have heq (g : Field.absoluteGaloisGroup ℚ) (x : K ⊗[O] Λ) :
      e ((latticeGaloisRep ρK Λ hΛ hOK).baseChange K g x) = ρK g (e x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      rw [GaloisRep.baseChange_tmul, het, het, map_smul]
      rfl
    | add x y hx hy => simp [hx, hy]
  refine ⟨e, ?_⟩
  ext g x
  change e ((latticeGaloisRep ρK Λ hΛ hOK).baseChange K g (e.symm x)) = ρK g x
  rw [heq, e.apply_symm_apply]

end ThreeAdicPlan
