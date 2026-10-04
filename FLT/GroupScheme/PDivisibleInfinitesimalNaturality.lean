/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleNilpotentCotangent
public import FLT.GroupScheme.AugmentationCotangentNaturality

/-! # Coefficient naturality of the original infinitesimal cotangent functional -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D E : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E]
  (X : PDivisibleSystem R K p height)
  (q : B →ₐ[R] C) (q' : D →ₐ[R] E) (β : B →ₐ[R] D) (γ : C →ₐ[R] E)
  (hc : q'.comp β = γ.comp q)

/-- A commuting square acts on the original infinitesimal point colimit. -/
def infinitesimalColimitMap (x : X.InfinitesimalColimit q) : X.InfinitesimalColimit q' :=
  ⟨X.pointColimitMap β x.val, by
    rw [← X.pointColimitMap_comp, hc, X.pointColimitMap_comp, x.property,
      X.pointColimitMap_mk]
    apply congrArg (X.pointColimitMk 0)
    ext a
    exact γ.commutes _⟩

/-- At each original finite level this is the actual augmentation-kernel map. -/
theorem infinitesimalColimitMap_mk (n : ℕ) (f : X.LevelInfinitesimalKernel q n) :
    X.infinitesimalColimitMap q q' β γ hc (X.infinitesimalColimitMk q n f) =
      X.infinitesimalColimitMk q' n
        (AlgHom.augmentationKernelMap q q' β γ hc _ f) := rfl

variable [∀ n, Finite (X.LevelCotangent n)]

/-- Cotangent extraction commutes with the actual map of square-zero coefficient kernels. -/
theorem formalInfinitesimalCotangentEquiv_natural
    (hJ : RingHom.ker q ^ 2 = ⊥) (hJ' : RingHom.ker q' ^ 2 = ⊥)
    (r s : ℕ) (hr : ∀ b : RingHom.ker q, p ^ r • b = 0)
    (hs : ∀ d : RingHom.ker q', p ^ s • d = 0) (x : X.InfinitesimalColimit q) :
    X.formalInfinitesimalCotangentEquiv q' hJ' s hs (X.infinitesimalColimitMap q q' β γ hc x) =
      (AlgHom.reductionKernelMap q q' β γ hc).comp
        (X.formalInfinitesimalCotangentEquiv q hJ r hr x) := by
  obtain ⟨f, rfl⟩ := X.infinitesimalColimitMk_surjective q hJ r hr x
  rw [X.infinitesimalColimitMap_mk, X.formalInfinitesimalCotangentEquiv_mk,
    X.formalInfinitesimalCotangentEquiv_mk]
  unfold infinitesimalLimitPairing
  rw [AlgHom.augmentationPointCotangentEquiv_natural]
  rfl

/-- Nilpotence supplies the exponents; the functional remains natural without a chosen bound. -/
theorem nilpotentInfinitesimalCotangentEquiv_natural
    (hJ : RingHom.ker q ^ 2 = ⊥) (hJ' : RingHom.ker q' ^ 2 = ⊥)
    (hB : IsNilpotent (p : B)) (hD : IsNilpotent (p : D)) (x : X.InfinitesimalColimit q) :
    X.nilpotentInfinitesimalCotangentEquiv q' hJ' hD (X.infinitesimalColimitMap q q' β γ hc x) =
      (AlgHom.reductionKernelMap q q' β γ hc).comp
        (X.nilpotentInfinitesimalCotangentEquiv q hJ hB x) :=
  X.formalInfinitesimalCotangentEquiv_natural q q' β γ hc hJ hJ' _ _ _ _ x

end ThreeAdicPlan.PDivisibleSystem
