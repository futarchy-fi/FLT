/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleFormalSmoothness
public import FLT.GroupScheme.PDivisibleInfinitesimalPairing

/-! # The original cotangent limit represents infinitesimal points of the smooth point functor -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
  (r : ℕ) (hr : ∀ b : RingHom.ker q, p ^ r • b = 0)

/-- The actual infinitesimal kernel of the original point functor is represented by its
original cotangent inverse limit. Finite level sets supply the proved limit reduction theorem. -/
def formalInfinitesimalCotangentEquiv :
    X.InfinitesimalColimit q ≃ (X.cotangentLimit →ₗ[R] RingHom.ker q) :=
  (X.infinitesimalColimitCotangentEquiv q hJ r hr).trans (X.cotangentTorsionEquiv r hr).toEquiv

/-- At the torsion level the comparison is exactly the original evaluation pairing. -/
theorem formalInfinitesimalCotangentEquiv_mk_torsion (f : X.LevelInfinitesimalKernel q r) :
    X.formalInfinitesimalCotangentEquiv q hJ r hr (X.infinitesimalColimitMk q r f) =
      X.infinitesimalLimitPairing q hJ r f := by
  change X.cotangentTorsionEquiv r hr (AlgHom.augmentationPointCotangentEquiv _ q hJ
    ((X.infinitesimalColimitEquiv q hJ r hr).symm
      ((X.infinitesimalColimitEquiv q hJ r hr) f))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Every original finite level, not only the chosen torsion level, retains the same pairing. -/
theorem formalInfinitesimalCotangentEquiv_mk (n : ℕ) (f : X.LevelInfinitesimalKernel q n) :
    X.formalInfinitesimalCotangentEquiv q hJ r hr (X.infinitesimalColimitMk q n f) =
      X.infinitesimalLimitPairing q hJ n f := by
  obtain ⟨g, hg⟩ := X.infinitesimalColimitMk_surjective q hJ r hr (X.infinitesimalColimitMk q n f)
  rw [← hg, X.formalInfinitesimalCotangentEquiv_mk_torsion q hJ r hr]
  exact X.infinitesimalLimitPairing_eq_of_colimit_eq q hJ g f hg

/-- The identification is independent of the chosen power annihilating the test kernel. -/
theorem formalInfinitesimalCotangentEquiv_independent
    (s : ℕ) (hs : ∀ b : RingHom.ker q, p ^ s • b = 0) :
    X.formalInfinitesimalCotangentEquiv q hJ r hr =
      X.formalInfinitesimalCotangentEquiv q hJ s hs := by
  ext z
  obtain ⟨f, rfl⟩ := X.infinitesimalColimitMk_surjective q hJ r hr z
  rw [X.formalInfinitesimalCotangentEquiv_mk q hJ r hr,
    X.formalInfinitesimalCotangentEquiv_mk q hJ s hs]

end ThreeAdicPlan.PDivisibleSystem
