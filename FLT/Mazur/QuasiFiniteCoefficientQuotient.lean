/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatCoefficientIdeal
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Quasi-finite quotients after coefficient change and localization

Quasi-finiteness keeps the full quotient finite on every field fiber, even
when an affine open of a finite family is no longer finite over the base.
The statements retain the actual extended ideal, including nilpotents.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.FCurve
variable {R S B D : Type u} [CommRing R] [CommRing S] [CommRing B] [CommRing D]
  [Algebra R S] [Algebra R B]

/-- The actual coefficient quotient inherits quasi-finiteness. -/
theorem quasiFinite_coefficient_ideal_quotient (I : Ideal B)
    [Algebra.QuasiFinite R (B ⧸ I)] :
    Algebra.QuasiFinite S ((S ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) :=
  Algebra.QuasiFinite.of_surjective_algHom
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S B S I).toAlgHom
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S B S I).surjective

/-- Every field coefficient change of a quasi-finite quotient is Artinian. -/
theorem artinian_coefficient_ideal_quotient {K : Type u} [Field K] [Algebra R K]
    (I : Ideal B) [Algebra.QuasiFinite R (B ⧸ I)] :
    IsArtinianRing ((K ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) := by
  let _ := quasiFinite_coefficient_ideal_quotient (R := R) (S := K) I
  let _ := Module.Finite.of_quasiFinite
    (R := K) (S := (K ⊗[R] B) ⧸ I.map (Algebra.TensorProduct.includeRight (A := K)))
  exact .of_finite K _

variable [Algebra R D] [Algebra B D] [IsScalarTower R B D]

/-- Restricting the ambient to any localization preserves quasi-finiteness of its quotient. -/
theorem quasiFinite_localized_ideal_quotient (M : Submonoid B) [IsLocalization M D]
    (I : Ideal B) [Algebra.QuasiFinite R (B ⧸ I)] :
    Algebra.QuasiFinite R (D ⧸ I.map (algebraMap B D)) := by
  let _ : IsScalarTower R (B ⧸ I) (D ⧸ I.map (algebraMap B D)) := .to₁₃₄ R B _ _
  exact Algebra.QuasiFinite.of_isLocalization (Algebra.algebraMapSubmonoid (B ⧸ I) M)

end FLT.Mazur.FCurve
