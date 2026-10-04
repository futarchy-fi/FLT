/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleInfinitesimalStages

/-! # The actual colimit infinitesimal kernel is represented at the torsion level -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height)

/-- Every original augmentation represents the same point in the actual colimit. -/
theorem pointColimitMk_augmentation (n : ℕ) :
    X.pointColimitMk n (X.levelAugmentation (B := B) n) =
      X.pointColimitMk 0 (X.levelAugmentation 0) := by
  rw [← X.pointInclusion_augmentation (Nat.zero_le n)]
  exact X.pointColimitMk_inclusion _ _

/-- Kernel of reduction at the actual colimit augmentation point. -/
def InfinitesimalColimit (q : B →ₐ[R] C) :=
  {z : X.PointColimit B //
    X.pointColimitMap q z = X.pointColimitMk 0 (X.levelAugmentation 0)}

/-- The original finite-stage kernel maps into the actual colimit kernel. -/
def infinitesimalColimitMk (q : B →ₐ[R] C) (n : ℕ)
    (f : X.LevelInfinitesimalKernel q n) : X.InfinitesimalColimit q :=
  ⟨X.pointColimitMk n f.val, by
    rw [X.pointColimitMap_mk, f.property]
    exact X.pointColimitMk_augmentation n⟩

/-- No finite-stage infinitesimal point is lost in the colimit. -/
theorem infinitesimalColimitMk_injective (q : B →ₐ[R] C) (n : ℕ) :
    Function.Injective (X.infinitesimalColimitMk q n) := by
  intro f g h
  apply Subtype.ext
  exact X.pointColimitMk_injective n (congrArg Subtype.val h)

/-- Every colimit infinitesimal point has a representative in the original level r. -/
theorem infinitesimalColimitMk_surjective (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) (r : ℕ)
    (hM : ∀ a : RingHom.ker q, p ^ r • a = 0) :
    Function.Surjective (X.infinitesimalColimitMk q r) := by
  intro z
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk _ z.val
  change z.val = X.pointColimitMk n x at hx
  have hq : q.comp x = X.levelAugmentation n := by
    apply X.pointColimitMk_injective n
    change X.pointColimitMap q (X.pointColimitMk n x) = _
    rw [← hx, z.property]
    exact (X.pointColimitMk_augmentation n).symm
  let f : X.LevelInfinitesimalKernel q n := ⟨x, hq⟩
  let g := X.infinitesimalInclusion q (Nat.le_max_right r n) f
  let e := X.infinitesimalStageEquiv q hJ (Nat.le_max_left r n) hM
  refine ⟨e.symm g, ?_⟩
  apply Subtype.ext
  have he : X.infinitesimalInclusion q (Nat.le_max_left r n) (e.symm g) = g := by
    rw [← X.infinitesimalStageEquiv_apply q hJ _ hM]
    exact e.apply_symm_apply g
  change X.pointColimitMk r (e.symm g).val = z.val
  calc
    _ = X.pointColimitMk (max r n)
        (X.infinitesimalInclusion q (Nat.le_max_left r n) (e.symm g)).val :=
      (X.pointColimitMk_inclusion _ _).symm
    _ = X.pointColimitMk (max r n) g.val := congrArg (fun t ↦ X.pointColimitMk _ t.val) he
    _ = X.pointColimitMk n x := X.pointColimitMk_inclusion _ _
    _ = z.val := hx.symm

/-- The actual level-r kernel is equivalent to the actual colimit kernel. -/
def infinitesimalColimitEquiv (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
    (r : ℕ) (hM : ∀ a : RingHom.ker q, p ^ r • a = 0) :
    X.LevelInfinitesimalKernel q r ≃ X.InfinitesimalColimit q :=
  Equiv.ofBijective (X.infinitesimalColimitMk q r)
    ⟨X.infinitesimalColimitMk_injective q r, X.infinitesimalColimitMk_surjective q hJ r hM⟩

/-- The colimit kernel is represented by the original cotangent pairing at level r. -/
def infinitesimalColimitCotangentEquiv (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) (r : ℕ)
    (hM : ∀ a : RingHom.ker q, p ^ r • a = 0) :
    X.InfinitesimalColimit q ≃ (X.LevelCotangent r →ₗ[R] RingHom.ker q) :=
  (X.infinitesimalColimitEquiv q hJ r hM).symm.trans
    (AlgHom.augmentationPointCotangentEquiv _ q hJ)

end ThreeAdicPlan.PDivisibleSystem
