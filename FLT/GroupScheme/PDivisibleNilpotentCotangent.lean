/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleFormalCotangent
public import FLT.GroupScheme.PDivisibleCotangentFiniteSets

/-! # Cotangent identification on p-nilpotent test algebras at the original rational place -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥) (hB : IsNilpotent (p : B))

/-- Nilpotence supplies the torsion exponent for the original cotangent identification. -/
def nilpotentInfinitesimalCotangentEquiv :
    X.InfinitesimalColimit q ≃ (X.cotangentLimit →ₗ[R] RingHom.ker q) :=
  X.formalInfinitesimalCotangentEquiv q hJ hB.choose (fun b ↦ by
    apply Subtype.ext
    change p ^ hB.choose • (b : B) = 0
    rw [nsmul_eq_mul, Nat.cast_pow, hB.choose_spec, zero_mul])

/-- The internally chosen exponent does not change any original finite-level pairing. -/
theorem nilpotentInfinitesimalCotangentEquiv_mk (n : ℕ) (f : X.LevelInfinitesimalKernel q n) :
    X.nilpotentInfinitesimalCotangentEquiv q hJ hB (X.infinitesimalColimitMk q n f) =
      X.infinitesimalLimitPairing q hJ n f :=
  X.formalInfinitesimalCotangentEquiv_mk q hJ _ _ n f

end ThreeAdicPlan.PDivisibleSystem
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
  {B C : Type} [CommRing B] [CommRing C]
  [Algebra ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) B]
  [Algebra ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) C]

/-- At the original rational place, finite-level finiteness is proved rather than assumed. -/
def rationalPlaceFormalInfinitesimalCotangentEquiv
    (q : B →ₐ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) (hB : IsNilpotent (p : B)) :
    X.InfinitesimalColimit q ≃ (X.cotangentLimit →ₗ[
      (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] RingHom.ker q) := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := rationalPlace_levelCotangent_finite X n
  exact X.nilpotentInfinitesimalCotangentEquiv q hJ hB

end ThreeAdicPlan
