/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

import all Mathlib.RingTheory.Grassmannian

public import FLT.Mazur.GrassmannianOriginalBaseChartCover
public import FLT.Mazur.GrassmannianLocalizedColumnBasis

/-!
# Local chart membership for the actual Grassmannian functor map

Localization of a selected column map is compared with the tensor quotient map
used by `Module.Grassmannian.map`. Its kernel is the full original base-changed
relation, not a replacement relation obtained by choosing quotient coordinates.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
/-- A column map is recovered from its values on the standard basis. -/
theorem selectedColumnMap_basisValues {S Q : Type u} [CommRing S]
    [AddCommGroup Q] [Module S Q] {d : ℕ} (f : (Fin d → S) →ₗ[S] Q) :
    selectedColumnMap (fun j ↦ f (Pi.basisFun S (Fin d) j)) = f := by
  rw [selectedColumnMap]
  exact (Pi.basisFun S (Fin d)).constr_self S f

variable {R A B M κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

omit [Algebra A B] [IsScalarTower R A B] [Fintype κ] in
/-- Equal coefficient algebra structures give the same full base-changed relation. -/
theorem baseChangeMkQ_ker_algebra_congr (a₁ a₂ : Algebra A B) (h : a₁ = a₂)
    (t₁ : letI := a₁; IsScalarTower R A B) (t₂ : letI := a₂; IsScalarTower R A B)
    (N : Submodule A (A ⊗[R] M)) :
    (letI := a₁; letI := t₁; (Module.Grassmannian.baseChangeMkQ B N).ker) =
      (letI := a₂; letI := t₂; (Module.Grassmannian.baseChangeMkQ B N).ker) := by
  subst a₂
  rfl

/-- The tensor quotient used by the functor preserves the original selected columns. -/
theorem baseChangeMkQ_selected_basis (N : Module.Grassmannian A (A ⊗[R] M) d)
    (i : AmbientChartIndex R M κ d) (j : Fin d) :
    Module.Grassmannian.baseChangeMkQ B N.toSubmodule
      (ambientChartSelected (ambientChartBaseChange B i) (Pi.basisFun B (Fin d) j)) =
      (1 : B) ⊗ₜ[A] N.toSubmodule.mkQ
        (ambientChartSelected (ambientChartBaseChange A i) (Pi.basisFun A (Fin d) j)) := by
  rw [ambientChartBaseChange_selected_basis, ambientChartBaseChange_selected_basis]
  simp only [Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul]

/-- All columns of the actual tensor quotient map agree with tensor extension of the old map. -/
theorem baseChangeMkQ_selected_map (N : Module.Grassmannian A (A ⊗[R] M) d)
    (i : AmbientChartIndex R M κ d) :
    (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).comp
      (ambientChartSelected (ambientChartBaseChange B i)) =
      selectedColumnMap (fun j ↦ (1 : B) ⊗ₜ[A] N.toSubmodule.mkQ
        (ambientChartSelected (ambientChartBaseChange A i) (Pi.basisFun A (Fin d) j))) := by
  apply (Pi.basisFun B (Fin d)).ext
  intro j
  rw [LinearMap.comp_apply, baseChangeMkQ_selected_basis]
  simp only [selectedColumnMap, Module.Basis.constr_basis]

/-- Bijectivity in the tensor quotient gives membership for the actual functor image. -/
theorem grassmannian_map_selected_bijective (N : Module.Grassmannian A (A ⊗[R] M) d)
    (i : AmbientChartIndex R M κ d)
    (h : Function.Bijective ((Module.Grassmannian.baseChangeMkQ B N.toSubmodule).comp
      (ambientChartSelected (ambientChartBaseChange B i)))) :
    Function.Bijective
      ((Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule.mkQ.comp
        (ambientChartSelected (ambientChartBaseChange B i))) := by
  have hN : (Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).ker := by
    have ha : (IsScalarTower.toAlgHom R A B).toAlgebra = ‹Algebra A B› :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    have ht := Module.Grassmannian.map_toSubmodule (IsScalarTower.toAlgHom R A B) N
    exact ht.trans (baseChangeMkQ_ker_algebra_congr _ _ ha _ _ N.toSubmodule)
  let e := (Submodule.quotEquivOfEq _ _ hN).trans
    (Module.Grassmannian.baseChangeMkQEquiv (B := B) N.toSubmodule)
  have hc : e.toLinearMap.comp
      ((Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule.mkQ.comp
        (ambientChartSelected (ambientChartBaseChange B i))) =
      (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).comp
        (ambientChartSelected (ambientChartBaseChange B i)) := by
    apply LinearMap.ext
    intro x
    simp only [e, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      Module.Grassmannian.baseChangeMkQEquiv,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  have hh : Function.Bijective (e.toLinearMap.comp
      ((Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule.mkQ.comp
        (ambientChartSelected (ambientChartBaseChange B i)))) := by
    rw [hc]
    exact h
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp hh

omit [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] in
/-- A principal selected-column isomorphism gives a chart for the localized functor point. -/
theorem grassmannian_localized_selected_bijective
    (N : Module.Grassmannian A (A ⊗[R] M) d) (i : AmbientChartIndex R M κ d) (r : A)
    (h : Function.Bijective (LocalizedModule.map (.powers r)
      (N.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i))))) :
    Function.Bijective
      ((Module.Grassmannian.map
        (IsScalarTower.toAlgHom R A (Localization.Away r)) N).toSubmodule.mkQ.comp
        (ambientChartSelected (ambientChartBaseChange (Localization.Away r) i))) := by
  apply grassmannian_map_selected_bijective
  rw [baseChangeMkQ_selected_map]
  apply tensorLocalizedColumnMap_bijective
  have hc := selectedColumnMap_basisValues
    (N.toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange A i)))
  simp only [LinearMap.comp_apply] at hc
  rw [hc]
  exact h

omit [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] in
/-- The actual localized functor point belongs to an original-base chart near every prime. -/
theorem exists_functor_localized_chart {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R M) (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d) (p : PrimeSpectrum A) :
    ∃ (i : AmbientChartIndex R M κ d) (r : A), r ∉ p.asIdeal ∧
      Function.Bijective
        ((Module.Grassmannian.map
        (IsScalarTower.toAlgHom R A (Localization.Away r)) N).toSubmodule.mkQ.comp
          (ambientChartSelected (ambientChartBaseChange (Localization.Away r) i))) := by
  obtain ⟨i, r, hr, hi⟩ := exists_original_base_chart_away b N hκ p
  exact ⟨i, r, hr, grassmannian_localized_selected_bijective N i r hi⟩

end FLT.Mazur.GrassmannianChart
