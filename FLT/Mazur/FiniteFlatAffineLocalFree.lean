/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Actual local freeness for finite flat finitely presented morphisms

On each affine base open the actual coordinate algebra is a finite projective
module. At every prime it becomes free on a principal neighborhood, with rank
equal to its rank at that prime. No Noetherian or reducedness condition is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {D S : Scheme.{u}} (g : D ⟶ S)
  [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (U : S.affineOpens)

omit [Flat g] in
/-- The actual affine coordinate algebra is finitely presented as a module. -/
theorem finiteFlat_app_finitePresentation :
    let _ := (g.app U).hom.toAlgebra
    Module.FinitePresentation Γ(S, U) Γ(D, g ⁻¹ᵁ U) := by
  let _ := (g.app U).hom.toAlgebra
  let _ : Module.Finite Γ(S, U) Γ(D, g ⁻¹ᵁ U) := g.finite_app U U.2
  have hp := g.finitePresentation_appLE U.2 (U.2.preimage g) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hp
  let _ : Algebra.FinitePresentation Γ(S, U) Γ(D, g ⁻¹ᵁ U) := hp
  exact Module.FinitePresentation.of_finite_of_finitePresentation _ _

/-- Finite flat affine coordinate algebras are projective over every affine base open. -/
theorem finiteFlat_app_projective :
    let _ := (g.app U).hom.toAlgebra
    Module.Projective Γ(S, U) Γ(D, g ⁻¹ᵁ U) := by
  let _ := (g.app U).hom.toAlgebra
  let _ := finiteFlat_app_finitePresentation g U
  have hf := g.flat_appLE U.2 (U.2.preimage g) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hf
  let _ : Module.Flat Γ(S, U) Γ(D, g ⁻¹ᵁ U) := hf
  exact Module.Flat.projective_of_finitePresentation

/-- Every prime has a principal neighborhood on which the actual finite algebra is free. -/
theorem finiteFlat_app_exists_free (p : PrimeSpectrum Γ(S, U)) :
    let _ := (g.app U).hom.toAlgebra
    ∃ r : Γ(S, U), r ∉ p.asIdeal ∧
      Module.Free (Localization.Away r) (LocalizedModule.Away r Γ(D, g ⁻¹ᵁ U)) ∧
      Module.finrank (Localization.Away r) (LocalizedModule.Away r Γ(D, g ⁻¹ᵁ U)) =
        Module.rankAtStalk Γ(D, g ⁻¹ᵁ U) p := by
  let _ := (g.app U).hom.toAlgebra
  let _ := finiteFlat_app_finitePresentation g U
  let _ := finiteFlat_app_projective g U
  let R := Γ(S, U)
  let M := Γ(D, g ⁻¹ᵁ U)
  let _ : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) :=
    Module.free_of_flat_of_isLocalRing
  exact Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (Localization.AtPrime p.asIdeal)

end FLT.Mazur.FCurve
