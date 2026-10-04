/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.QuasiFiniteUnitCover
public import FLT.Mathlib.RingTheory.MvPolynomial.PrincipalRelationBaseChange
public import FLT.Mathlib.RingTheory.MvPolynomial.UnitIdealCertificateStage

/-! # Enlarge a coefficient stage until its quasi-finite principal charts cover -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

universe u
variable {R : Type u} {σ : Type} {ι κ : Type*} [CommRing R] [Finite ι] [Finite κ]

/-- Descend the unit-ideal certificate and base-change the good principal charts to the
enlarged stage. The result proves quasi-finiteness at that stage, not merely at the final base. -/
theorem exists_quasiFinite_stage_of_principal_cover (S : Subalgebra ℤ R) (hS : S.FG)
    (f : ι → MvPolynomial σ S) (g : κ → MvPolynomial σ S)
    (hcover : Ideal.span (Set.range fun j ↦ Ideal.Quotient.mk
      (Ideal.span (Set.range fun i ↦ map S.val.toRingHom (f i)))
      (map S.val.toRingHom (g j))) = ⊤)
    (hgood : ∀ j, Algebra.QuasiFinite S
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j)))) :
    ∃ (T : Subalgebra ℤ R) (hST : S ≤ T), T.FG ∧ IsNoetherianRing T ∧
      Algebra.QuasiFinite T (MvPolynomial σ T ⧸ Ideal.span
        (Set.range fun i ↦ map (Subalgebra.inclusion hST).toRingHom (f i))) := by
  obtain ⟨T, hST, hT, hN, hspan⟩ :=
    exists_unitIdeal_certificate_stage_of_stage S hS f g hcover
  let : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  refine ⟨T, hST, hT, hN, ?_⟩
  apply Algebra.quasiFinite_of_unit_principal_cover _ hspan
  intro j
  have := hgood j
  exact (Algebra.QuasiFinite.iff_of_algEquiv
    (principalRelationBaseChangeEquiv (S := T) f (g j))).mp inferInstance

end MvPolynomial
