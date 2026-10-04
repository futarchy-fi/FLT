/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTangentReduction

/-! # Naturality of torsion tangent comparisons for the actual integral systems -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K M : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [AddCommGroup M] [Module R M] {X Y : PDivisibleSystem R K p height}
  [∀ n, Finite (X.LevelCotangent n)] [∀ n, Finite (Y.LevelCotangent n)]

/-- The torsion comparison commutes with the specified original system morphism. -/
theorem Hom.cotangentTorsion_naturality (f : Hom X Y) (n : ℕ)
    (hM : ∀ a : M, p ^ n • a = 0) (d : X.LevelCotangent n →ₗ[R] M) :
    Y.cotangentTorsionEquiv n hM (d.comp (ModelHom.cotangentMap (f.app n))) =
      (X.cotangentTorsionEquiv n hM d).comp f.cotangentMap := by
  ext y
  change d (ModelHom.cotangentMap (f.app n) (Y.cotangentEval n y)) =
    d (X.cotangentEval n (f.cotangentMap y))
  rw [Hom.cotangentMap_eval]

/-- Naturality also holds for the original finite-level Leibniz functionals. -/
theorem Hom.tangentTorsion_naturality (f : Hom X Y) (n : ℕ)
    (hM : ∀ a : M, p ^ n • a = 0) (d : (X.level n).Tangent (M := M)) :
    Y.tangentTorsionEquiv n hM (ModelHom.tangentMap (f.app n) d) =
      (X.tangentTorsionEquiv n hM d).comp f.cotangentMap := by
  obtain ⟨d, rfl⟩ := (X.level n).cotangentTangentEquiv.surjective d
  rw [ModelHom.cotangentTangent_naturality]
  simpa only [tangentTorsionEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    f.cotangentTorsion_naturality n hM d

end ThreeAdicPlan.PDivisibleSystem
