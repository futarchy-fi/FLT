/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorIdealPullback
public import FLT.Mazur.ProjectiveIdealVanishingScheme

/-!
# Geometric tests for the projective ideal vanishing scheme

The coefficient chart represents zero of the actual pulled ideal on the
geometric fiber product. This identifies its algebraic test condition with
scheme-theoretic vanishing, for arbitrary test algebras.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ProjectiveIdealVanishing
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Projective R B] (J : Ideal B) (A : Type) [CommRing A] [Algebra R A]

/-- The closed coefficient chart represents actual geometric ideal vanishing. -/
theorem geometric_factorization_iff :
    (∃ g : Spec (.of A) ⟶ scheme R B J,
      g ≫ inclusion R B J = Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
        (BaseAdicThickening.baseIdeal (.of B) J).comap
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
            (Spec.map (CommRingCat.ofHom (algebraMap R B)))) = ⊥ := by
  rw [factorization_iff, AffineTensorIdealPullback.pullbackIdeal_eq_bot_iff]

/-- The universal chart kills the geometric ideal, without reducing the fiber product. -/
theorem quotient_geometricIdeal_eq_bot :
    (BaseAdicThickening.baseIdeal (.of B) J).comap
      (pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ ideal R B J))))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))) = ⊥ := by
  rw [AffineTensorIdealPullback.pullbackIdeal_eq_bot_iff]
  exact quotient_extendedIdeal_eq_bot R B J

end FLT.Mazur.ProjectiveIdealVanishing
