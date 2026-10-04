/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleInfinitesimalColimit
public import FLT.GroupScheme.PDivisibleTangentReduction
public import FLT.GroupScheme.PDivisibleColimitLifting

/-! # Original infinitesimal points pair coherently with the cotangent limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height) (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

/-- Cotangent extraction commutes with the original inclusion on infinitesimal points. -/
theorem infinitesimalInclusion_cotangent {m n : ℕ} (h : m ≤ n)
    (f : X.LevelInfinitesimalKernel q m) :
    AlgHom.augmentationPointCotangentEquiv _ q hJ (X.infinitesimalInclusion q h f) =
      (AlgHom.augmentationPointCotangentEquiv _ q hJ f).comp (X.cotangentRestriction h) := by
  apply (X.level n).cotangentTangentEquiv.injective
  change (X.level n).cotangentTangentEquiv
    ((X.level n).cotangentTangentEquiv.symm (AlgHom.augmentationPointToTangent _ q hJ _)) = _
  rw [LinearEquiv.apply_symm_apply]
  change AlgHom.augmentationPointToTangent _ q hJ _ =
    (X.level n).cotangentTangentEquiv
      ((AlgHom.augmentationPointCotangentEquiv _ q hJ f).comp (X.inclusion h).cotangentMap)
  rw [← ModelHom.cotangentTangent_naturality]
  change AlgHom.augmentationPointToTangent _ q hJ _ =
    (X.inclusion h).tangentMap ((X.level m).cotangentTangentEquiv
      ((X.level m).cotangentTangentEquiv.symm (AlgHom.augmentationPointToTangent _ q hJ f)))
  rw [LinearEquiv.apply_symm_apply]
  exact X.infinitesimalInclusion_tangent q hJ h f

/-- The pairing uses the specified original finite-level evaluation of the inverse limit. -/
def infinitesimalLimitPairing (n : ℕ) (f : X.LevelInfinitesimalKernel q n) :
    X.cotangentLimit →ₗ[R] RingHom.ker q :=
  (AlgHom.augmentationPointCotangentEquiv _ q hJ f).comp (X.cotangentEval n)

/-- Passing to any higher original level preserves the same limit functional. -/
theorem infinitesimalLimitPairing_inclusion {m n : ℕ} (h : m ≤ n)
    (f : X.LevelInfinitesimalKernel q m) :
    X.infinitesimalLimitPairing q hJ n (X.infinitesimalInclusion q h f) =
      X.infinitesimalLimitPairing q hJ m f := by
  unfold infinitesimalLimitPairing
  rw [X.infinitesimalInclusion_cotangent q hJ h f]
  apply LinearMap.ext
  intro a
  change (AlgHom.augmentationPointCotangentEquiv _ q hJ f)
    (X.cotangentRestriction h (X.cotangentEval n a)) = _
  rw [X.cotangentEval_restriction]
  rfl

/-- Equality in the actual point colimit implies equality of the original cotangent pairings. -/
theorem infinitesimalLimitPairing_eq_of_colimit_eq {m n : ℕ}
    (f : X.LevelInfinitesimalKernel q m) (g : X.LevelInfinitesimalKernel q n)
    (he : X.infinitesimalColimitMk q m f = X.infinitesimalColimitMk q n g) :
    X.infinitesimalLimitPairing q hJ m f = X.infinitesimalLimitPairing q hJ n g := by
  obtain ⟨k, hm, hn, hk⟩ := (X.pointColimitMk_eq_iff f.val g.val).mp (congrArg Subtype.val he)
  have hk' : X.infinitesimalInclusion q hm f = X.infinitesimalInclusion q hn g :=
    Subtype.ext hk
  rw [← X.infinitesimalLimitPairing_inclusion q hJ hm,
    ← X.infinitesimalLimitPairing_inclusion q hJ hn, hk']

end ThreeAdicPlan.PDivisibleSystem
