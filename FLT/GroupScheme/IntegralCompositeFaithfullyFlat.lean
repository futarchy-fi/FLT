/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CartierDualFaithfullyFlat
public import FLT.GroupScheme.FaithfullyFlatRetraction

/-!
# Faithfully flat descended quotient maps

The coordinate inclusion of an integral quotient splits linearly over a PID.
It stays injective on every residue fibre; the same holds for any factor of
that inclusion, and the finite Hopf criterion proves faithful flatness.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]
    {A H Q : FiniteFlatObject R}

/-- The coordinate inclusion of a quotient has a linear retraction over the base. -/
theorem FiniteFlatExtension.quotientLinearRetraction (E : FiniteFlatExtension A H Q) :
    ∃ s : H.model.CoordinateRing →ₗ[R] Q.model.CoordinateRing,
      s.comp E.quotient.toLinearMap = LinearMap.id := by
  let quotientAlgebra := E.quotient.toAlgHom.toRingHom.toAlgebra
  let quotientTower : IsScalarTower R Q.model.CoordinateRing H.model.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' E.quotient.toAlgHom.comp_algebraMap.symm
  let quotientFlat : Module.FaithfullyFlat Q.model.CoordinateRing H.model.CoordinateRing :=
    E.quotientFaithfullyFlat
  exact Algebra.faithfullyFlatLinearRetraction

/-- Arbitrary base change preserves injectivity of an integral quotient's coordinates. -/
theorem FiniteFlatExtension.quotientBaseChangeInjective (E : FiniteFlatExtension A H Q)
    (S : Type) [CommRing S] [Algebra R S] :
    Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id S S) E.quotient) := by
  obtain ⟨s, hs⟩ := E.quotientLinearRetraction
  apply Function.LeftInverse.injective (g := s.lTensor S)
  intro z
  change ((s.lTensor S).comp (E.quotient.toLinearMap.lTensor S)) z = z
  rw [← LinearMap.lTensor_comp, hs, LinearMap.lTensor_id]
  rfl

/-- An integral factor of a faithfully flat quotient is faithfully flat. -/
theorem FiniteFlatExtension.factorQuotientFaithfullyFlat
    (E : FiniteFlatExtension A H Q) {T : FiniteFlatObject R}
    (p : H.Hom T) (q : T.Hom Q) (h : p.comp q = E.quotient) :
    let _quotientAlgebra := q.toAlgHom.toRingHom.toAlgebra;
      Module.FaithfullyFlat Q.model.CoordinateRing T.model.CoordinateRing := by
  let quotientAlgebra := q.toAlgHom.toRingHom.toAlgebra
  let quotientTower : IsScalarTower R Q.model.CoordinateRing T.model.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' q.toAlgHom.comp_algebraMap.symm
  apply HopfAlgebra.faithfullyFlat_of_injective_residueBaseChange q (by ext; rfl)
  · intro x y hxy
    apply E.quotient_injective
    rw [← h]
    exact congrArg p hxy
  · intro I maximalI
    have he : (Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) p).comp
        (Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) q) =
        Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) E.quotient := by
      rw [← h]
      ext z
      induction z using TensorProduct.inductionOn with
      | tmul r x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    intro x y hxy
    apply E.quotientBaseChangeInjective (R ⧸ I)
    rw [← he]
    exact congrArg (Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) p) hxy

end ThreeAdicPlan
