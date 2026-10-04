/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTangentStabilization
public import FLT.GroupScheme.AugmentationKernelPrecomposition
public import FLT.GroupScheme.PDivisiblePointColimit

/-! # Original finite-stage infinitesimal kernels and their stabilization -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height)

/-- The augmentation point of the original level over a test algebra. -/
def levelAugmentation (n : ℕ) : (X.level n).CoordinateRing →ₐ[R] B :=
  (Algebra.ofId R B).comp (Bialgebra.counitAlgHom R (X.level n).CoordinateRing)

/-- The original inclusions preserve augmentation points. -/
theorem pointInclusion_augmentation {m n : ℕ} (h : m ≤ n) :
    X.pointInclusion h (X.levelAugmentation (B := B) m) = X.levelAugmentation n := by
  ext a
  change algebraMap R B (Coalgebra.counit (X.inclusion h a)) =
    algebraMap R B (Coalgebra.counit a)
  rw [CoalgHomClass.counit_comp_apply]

/-- The infinitesimal kernel of the specified reduction at an original level. -/
abbrev LevelInfinitesimalKernel (q : B →ₐ[R] C) (n : ℕ) :=
  (Bialgebra.counitAlgHom R (X.level n).CoordinateRing).AugmentationPointKernel q

/-- The original inclusion on the actual infinitesimal kernels. -/
def infinitesimalInclusion (q : B →ₐ[R] C) {m n : ℕ} (h : m ≤ n) :
    X.LevelInfinitesimalKernel q m → X.LevelInfinitesimalKernel q n := fun f ↦
  ⟨X.pointInclusion h f.val, by
    change (q.comp f.val).comp (X.inclusion h).toAlgHom = _
    rw [f.property]
    exact X.pointInclusion_augmentation h⟩

/-- Tangent extraction commutes with the original inclusion on actual kernels. -/
theorem infinitesimalInclusion_tangent (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) {m n : ℕ} (h : m ≤ n)
    (f : X.LevelInfinitesimalKernel q m) :
    AlgHom.augmentationPointToTangent _ q hJ (X.infinitesimalInclusion q h f) =
      (X.inclusion h).tangentMap (AlgHom.augmentationPointToTangent _ q hJ f) := by
  apply Subtype.ext
  ext a
  change f.val (X.inclusion h a) - algebraMap R B (Coalgebra.counit a) =
    f.val (X.inclusion h a) - algebraMap R B (Coalgebra.counit (X.inclusion h a))
  rw [CoalgHomClass.counit_comp_apply]

/-- Actual kernels stabilize at r when the actual reduction kernel is killed by p^r. -/
def infinitesimalStageEquiv (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
    {r n : ℕ} (h : r ≤ n) (hM : ∀ a : RingHom.ker q, p ^ r • a = 0) :
    X.LevelInfinitesimalKernel q r ≃ X.LevelInfinitesimalKernel q n :=
  (AlgHom.augmentationPointKernelEquiv _ q hJ).trans
    ((X.tangentStageEquiv h hM).toEquiv.trans
      (AlgHom.augmentationPointKernelEquiv _ q hJ).symm)

/-- Stabilization is induced by the given original inclusion, with no replacement model. -/
theorem infinitesimalStageEquiv_apply (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) {r n : ℕ} (h : r ≤ n)
    (hM : ∀ a : RingHom.ker q, p ^ r • a = 0) (f : X.LevelInfinitesimalKernel q r) :
    X.infinitesimalStageEquiv q hJ h hM f = X.infinitesimalInclusion q h f := by
  apply (AlgHom.augmentationPointKernelEquiv _ q hJ).injective
  change (AlgHom.augmentationPointKernelEquiv _ q hJ)
    ((AlgHom.augmentationPointKernelEquiv _ q hJ).symm
      (X.tangentStageEquiv h hM (AlgHom.augmentationPointKernelEquiv _ q hJ f))) = _
  rw [Equiv.apply_symm_apply, tangentStageEquiv_apply]
  exact (X.infinitesimalInclusion_tangent q hJ h f).symm

end ThreeAdicPlan.PDivisibleSystem
