/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleFormalCotangent
public import FLT.GroupScheme.AugmentationCotangentNaturality

/-! # Formal smoothness lifts functionals on the original cotangent limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [CommRing D] [Algebra R B] [Algebra R C] [Algebra R D]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]

/-- Across a surjective square-zero map of augmented test algebras, every represented
cotangent functional lifts, with its original kernel map retained. -/
theorem exists_cotangent_kernel_lift (q : B →ₐ[R] D) (q' : C →ₐ[R] D)
    (β : B →ₐ[R] C) (hc : q'.comp β = (AlgHom.id R D).comp q)
    (hβ : Function.Surjective β) (hker : RingHom.ker β ^ 2 = ⊥)
    (hB : IsNilpotent (p : B)) (hJ : RingHom.ker q ^ 2 = ⊥)
    (hJ' : RingHom.ker q' ^ 2 = ⊥) (r : ℕ)
    (hr : ∀ b : RingHom.ker q', p ^ r • b = 0)
    (f : X.cotangentLimit →ₗ[R] RingHom.ker q') :
    ∃ g : X.cotangentLimit →ₗ[R] RingHom.ker q,
      (AlgHom.reductionKernelMap q q' β (AlgHom.id R D) hc).comp g = f := by
  let e := X.cotangentTorsionEquiv r hr
  let a := (AlgHom.augmentationPointCotangentEquiv _ q' hJ').symm (e.symm f)
  obtain ⟨m, h, y, hy⟩ := X.exists_nilpotent_inclusion_lift β hβ ⟨2, hker⟩ hB r a.val
  have hyq : q.comp y = X.levelAugmentation m := by
    calc
      q.comp y = q'.comp (β.comp y) := by rw [← AlgHom.comp_assoc, hc]; rfl
      _ = (q'.comp a.val).comp (X.inclusion h).toAlgHom := by
        rw [hy, AlgHom.comp_assoc]
      _ = X.levelAugmentation m := by
        rw [a.property]
        exact X.pointInclusion_augmentation h
  let b : X.LevelInfinitesimalKernel q m := ⟨y, hyq⟩
  have hb : AlgHom.augmentationKernelMap q q' β (AlgHom.id R D) hc _ b =
      X.infinitesimalInclusion q' h a := Subtype.ext hy
  refine ⟨X.infinitesimalLimitPairing q hJ m b, ?_⟩
  calc
    _ = X.infinitesimalLimitPairing q' hJ' m
        (AlgHom.augmentationKernelMap q q' β (AlgHom.id R D) hc _ b) := by
      unfold infinitesimalLimitPairing
      rw [AlgHom.augmentationPointCotangentEquiv_natural]
      rfl
    _ = X.infinitesimalLimitPairing q' hJ' r a := by
      rw [hb, X.infinitesimalLimitPairing_inclusion]
    _ = f := by
      change e ((AlgHom.augmentationPointCotangentEquiv _ q' hJ') a) = f
      rw [Equiv.apply_symm_apply, e.apply_symm_apply]

end ThreeAdicPlan.PDivisibleSystem
