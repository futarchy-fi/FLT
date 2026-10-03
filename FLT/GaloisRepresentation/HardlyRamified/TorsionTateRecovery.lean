/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionTateSurjective
public import FLT.Deformations.RepresentationTheory.PadicLatticeCompletion
public import FLT.Deformations.RepresentationTheory.TorsionTensorCompletion
public import FLT.GroupScheme.PDivisibleTateModule

/-! # Recovering the original lattice from its geometric Tate tower -/

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
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

omit [IsDomain R] in
/-- The original point comparison carries reductions to the tensor quotient maps. -/
theorem torsionPoints_transition {m n : ℕ} (h : m ≤ n)
    (x : (hρ.torsionModelUniverses n).Points) :
    hρ.torsionPointsUniverses m (genericHom (hρ.torsionTransitionUniverses h) x) =
      tensorTransition (p : R) h (hρ.torsionPointsUniverses n x) := by
  rw [hρ.genericHom_torsionTransitionUniverses]
  exact (hρ.torsionPointsUniverses m).apply_symm_apply _

/-- Comparison of actual points with the completion's level quotients. -/
def torsionCompletionLevel (n : ℕ) : (hρ.torsionModelUniverses n).Points ≃+
    V ⧸ ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R V) :=
  (hρ.torsionPointsUniverses n).trans (tensorCompletionLevel (p : R) n).toAddEquiv

omit [IsDomain R] in
/-- The point-to-completion comparison respects every transition. -/
theorem torsionCompletionLevel_transition {m n : ℕ} (h : m ≤ n)
    (x : (hρ.torsionModelUniverses n).Points) :
    hρ.torsionCompletionLevel m (genericHom (hρ.torsionTransitionUniverses h) x) =
      AdicCompletion.transitionMap (Ideal.span {(p : R)}) V h (hρ.torsionCompletionLevel n x) := by
  change tensorCompletionLevel (p : R) m
    (hρ.torsionPointsUniverses m (genericHom (hρ.torsionTransitionUniverses h) x)) = _
  rw [hρ.torsionPoints_transition, tensorCompletionLevel_transition]
  rfl

/-- The actual geometric Tate limit is the adic completion of the original lattice. -/
def torsionTateCompletion : hρ.torsionPDivisibleUniverses.tateSequences ≃+
    AdicCompletion (Ideal.span {(p : R)}) V where
  toFun x := ⟨fun n ↦ hρ.torsionCompletionLevel n (x.val n), by
    intro m n h
    rw [← hρ.torsionCompletionLevel_transition]
    exact congrArg (hρ.torsionCompletionLevel m) (x.property h)⟩
  invFun x := ⟨fun n ↦ (hρ.torsionCompletionLevel n).symm (x.val n), by
    intro m n h
    apply (hρ.torsionCompletionLevel m).injective
    change hρ.torsionCompletionLevel m
      (genericHom (hρ.torsionTransitionUniverses h)
        ((hρ.torsionCompletionLevel n).symm (x.val n))) =
      hρ.torsionCompletionLevel m ((hρ.torsionCompletionLevel m).symm (x.val m))
    rw [hρ.torsionCompletionLevel_transition, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
    exact x.property h⟩
  left_inv x := by apply Subtype.ext; funext n; exact AddEquiv.symm_apply_apply _ _
  right_inv x := by apply Subtype.ext; funext n; exact AddEquiv.apply_symm_apply _ _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ _ _

/-- The original complete lattice is identified with its actual geometric Tate module. -/
def torsionTateRecovery : V ≃+ hρ.torsionPDivisibleUniverses.tateSequences :=
  (padicLatticeCompletion p R V).toAddEquiv.trans hρ.torsionTateCompletion.symm

/-- The recovered vector has exactly its original tensor residues. -/
theorem torsionTateRecovery_eval (n : ℕ) (x : V) :
    hρ.torsionPointsUniverses n
      (hρ.torsionPDivisibleUniverses.tateEval n (hρ.torsionTateRecovery x)) = 1 ⊗ₜ[R] x := by
  apply (tensorCompletionLevel (p : R) n).injective
  change hρ.torsionCompletionLevel n
    ((hρ.torsionCompletionLevel n).symm (Submodule.Quotient.mk x)) = _
  rw [AddEquiv.apply_symm_apply, tensorCompletionLevel_one_tmul]

/-- Recovery respects the actual local Galois representation on the original lattice. -/
theorem torsionTateRecovery_galois (g : Field.absoluteGaloisGroup
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) (x : V) :
    hρ.torsionTateRecovery (ρ.toLocal (LocalCyclotomic.rationalPlace p) g x) =
      g • hρ.torsionTateRecovery x := by
  apply hρ.torsionPDivisibleUniverses.tate_ext
  intro n
  apply (hρ.torsionPointsUniverses n).injective
  rw [hρ.torsionTateRecovery_eval, PDivisibleSystem.tateEval_smul,
    hρ.torsionPoints_smul_universes, hρ.torsionTateRecovery_eval]
  rfl

end GaloisRepresentation.IsHardlyRamified
