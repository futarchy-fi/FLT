/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SegreClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Reindexing homogeneous coordinates

Polynomial renaming induces an isomorphism of projective spaces, with the
expected formulas on standard charts. It gives the finite-dimensional target
of the Segre closed immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u v

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type (max u v)) [CommRing R] {ι κ : Type v}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Renaming variables preserves the standard grading. -/
def renameGraded (e : ι → κ) : grading R ι →+*ᵍ grading R κ where
  __ := (rename e : MvPolynomial ι R →ₐ[R] MvPolynomial κ R).toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous

@[simp]
lemma renameGraded_apply (e : ι → κ) (p : MvPolynomial ι R) :
    renameGraded R e p = rename e p := rfl

/-- Inverse coordinate renamings compose to the graded identity. -/
lemma renameGraded_symm_comp (e : ι ≃ κ) :
    (renameGraded R e.symm).comp (renameGraded R e) = .id (grading R ι) := by
  ext i
  simp [renameGraded]

/-- A bijective renaming carries the irrelevant ideal onto the irrelevant ideal. -/
lemma renameGraded_irrelevant (e : ι ≃ κ) :
    HomogeneousIdeal.irrelevant (grading R κ) ≤
      (HomogeneousIdeal.irrelevant (grading R ι)).map (renameGraded R e) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  have h := HomogeneousIdeal.mem_irrelevant_of_mem (grading R ι) hn
    (hp.rename_isHomogeneous (f := e.symm))
  have hm := Ideal.mem_map_of_mem (renameGraded R e).toRingHom h
  change p ∈ (HomogeneousIdeal.irrelevant (grading R ι)).toIdeal.map
    (renameGraded R e).toRingHom
  simpa using hm

/-- The isomorphism sending coordinate `i` to coordinate `e i`. -/
def reindexIso (e : ι ≃ κ) : space R ι ≅ space R κ where
  hom := Proj.map (renameGraded R e.symm) (renameGraded_irrelevant R e.symm)
  inv := Proj.map (renameGraded R e) (renameGraded_irrelevant R e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simpa only [renameGraded_symm_comp] using Proj.map_id (𝒜 := grading R ι)
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h := renameGraded_symm_comp R e.symm
    simp only [Equiv.symm_symm] at h
    simpa only [h] using Proj.map_id (𝒜 := grading R κ)

/-- Reindexing has the expected inverse. -/
lemma reindexIso_symm (e : ι ≃ κ) : (reindexIso R e).symm = reindexIso R e.symm := rfl

/-- Standard opens are permuted by the coordinate equivalence. -/
@[simp]
lemma reindexIso_preimage_chart (e : ι ≃ κ) (j : κ) :
    (reindexIso R e).hom ⁻¹ᵁ chart R κ j = chart R ι (e.symm j) := by
  change Proj.basicOpen _ (renameGraded R e.symm (X j)) = _
  simp [chart]

/-- Renaming on the homogeneous localizations of matching charts. -/
def reindexChartRingMap (e : ι ≃ κ) (j : κ) :
    chartRing R κ j →+* chartRing R ι (e.symm j) :=
  HomogeneousLocalization.map (renameGraded R e.symm) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

/-- Coordinate ratios transform by the same index equivalence. -/
@[simp]
lemma reindexChartRingMap_coordinate (e : ι ≃ κ) (j l : κ) :
    reindexChartRingMap R e j (coordinate R κ j l) =
      coordinate R ι (e.symm j) (e.symm l) := by
  apply val_injective
  simp [reindexChartRingMap, coordinate, Away.mk, HomogeneousLocalization.map_mk]

/-- Reindexing on an affine chart is the spectrum map of polynomial renaming. -/
@[reassoc]
lemma chartMap_reindexIso (e : ι ≃ κ) (j : κ) :
    chartMap R ι (e.symm j) ≫ (reindexIso R e).hom =
      Spec.map (CommRingCat.ofHom (reindexChartRingMap R e j)) ≫ chartMap R κ j := by
  have h (s : MvPolynomial ι R) (hs : renameGraded R e.symm (X j) = s)
      (hm : s ∈ grading R ι 1) :
      Proj.awayι (grading R ι) s hm (by decide) ≫ (reindexIso R e).hom =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (renameGraded R e.symm)
            (P := Submonoid.powers (X j)) (Q := Submonoid.powers s) (by
              rintro _ ⟨n, rfl⟩
              exact ⟨n, by simp [← hs]⟩))) ≫ chartMap R κ j := by
    subst s
    exact Proj.awayι_comp_map (renameGraded R e.symm)
      (renameGraded_irrelevant R e.symm) (by decide) (X j) (isHomogeneous_X R j)
  exact h (X (e.symm j)) (by simp) (isHomogeneous_X R (e.symm j))

/-- Reindexing is over the unchanged coefficient spectrum. -/
@[reassoc (attr := simp)]
lemma reindexIso_baseProjection (e : ι ≃ κ) :
    (reindexIso R e).hom ≫ baseProjection R κ = baseProjection R ι := by
  apply (standardChartCover R ι).hom_ext
  intro i
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  change chartMap R ι (e.symm j) ≫ _ = chartMap R ι (e.symm j) ≫ _
  rw [chartMap_reindexIso_assoc, chartMap_baseProjection, chartMap_baseProjection,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change reindexChartRingMap R e j (chartScalars R κ j r) =
    chartScalars R ι (e.symm j) r
  apply val_injective
  simp [reindexChartRingMap, chartScalars, constantsToZero,
    fromZeroRingHom, HomogeneousLocalization.map_mk]

variable (R : Type u) [CommRing R]

/-- The standard finite Segre target dimension. -/
def segreDimension (a b : ℕ) : ℕ := (a + 1) * (b + 1) - 1

lemma segreDimension_succ (a b : ℕ) :
    segreDimension a b + 1 = (a + 1) * (b + 1) :=
  Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))

/-- Pair coordinates enumerate exactly the positive number of Segre coordinates. -/
def segreCoordinateEquiv (a b : ℕ) :
    Fin (a + 1) × Fin (b + 1) ≃ Fin (segreDimension a b + 1) :=
  finProdFinEquiv.trans (finCongr (segreDimension_succ a b).symm)

/-- The Segre map with its target indexed by one finite ordinal. -/
def finiteSegreMorphism (a b : ℕ) :
    productSpace R (Fin (a + 1)) (Fin (b + 1)) ⟶
      space R (Fin (segreDimension a b + 1)) :=
  segreMorphism R (Fin (a + 1)) (Fin (b + 1)) ≫
    (reindexIso R (segreCoordinateEquiv a b)).hom

instance finiteSegreMorphism_isClosedImmersion (a b : ℕ) :
    IsClosedImmersion (finiteSegreMorphism R a b) := by
  dsimp [finiteSegreMorphism]
  infer_instance

@[reassoc (attr := simp)]
lemma finiteSegreMorphism_baseProjection (a b : ℕ) :
    finiteSegreMorphism R a b ≫ baseProjection R (Fin (segreDimension a b + 1)) =
      CategoryTheory.Limits.pullback.fst _ _ ≫ baseProjection R (Fin (a + 1)) := by
  simp only [finiteSegreMorphism, Category.assoc, reindexIso_baseProjection,
    segreMorphism_baseProjection]

end FLT.Mazur.ProjectiveSpace
