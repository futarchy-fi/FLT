/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealStalkDescent
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Faithfully flat detection of full ideal sheaves

Actual stalk ideals determine the entire ideal sheaf, including nilpotents.
Jointly surjective flat maps therefore detect equality of full ideals.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
variable {X Y : Scheme.{u}}

/-- Full ideal sheaves are determined by their actual structure-stalk ideals. -/
theorem idealSheaf_eq_of_stalkIdeal {I J : Y.IdealSheafData}
    (h : ∀ y : Y, stalkIdeal I y = stalkIdeal J y) : I = J := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let z : PrimeSpectrum Γ(Y, U.1) := ⟨P, hP.isPrime⟩
  let y : Y := U.2.fromSpec z
  have hy : y ∈ U.1 := by
    change y ∈ (U.1 : Set Y)
    rw [← U.2.range_fromSpec]
    exact ⟨z, rfl⟩
  let : Algebra Γ(Y, U.1) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have hz : U.2.primeIdealOf ⟨y, hy⟩ = z := by
    apply U.2.fromSpec.isOpenEmbedding.injective
    exact U.2.fromSpec_primeIdealOf ⟨y, hy⟩
  let : IsLocalization P.primeCompl (Y.presheaf.stalk y) := by
    have hl := U.2.isLocalization_stalk ⟨y, hy⟩
    simpa only [hz] using hl
  let e := IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk y)
    (Localization.AtPrime P)
  have he := congrArg (Ideal.map e.toRingHom) (h y)
  rw [stalkIdeal_eq_map I y U hy, stalkIdeal_eq_map J y U hy,
    Ideal.map_map, Ideal.map_map] at he
  have hc : e.toRingHom.comp (Y.presheaf.germ U.1 y hy).hom =
      algebraMap Γ(Y, U.1) (Localization.AtPrime P) := by
    ext r
    exact e.commutes r
  rwa [hc] at he

/-- A flat pullback detects the original ideal stalk at every point of its source. -/
theorem stalkIdeal_eq_of_flat_comap (f : X ⟶ Y) [Flat f]
    {I J : Y.IdealSheafData} (h : I.comap f = J.comap f) (x : X) :
    stalkIdeal I (f x) = stalkIdeal J (f x) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  let : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply Ideal.map_injective_of_faithfullyFlat (B := X.presheaf.stalk x)
  exact (stalkIdeal_comap I f x).symm.trans
    ((congrArg (fun K ↦ stalkIdeal K x) h).trans (stalkIdeal_comap J f x))

/-- Jointly surjective flat maps detect equality of entire ideal sheaves. -/
theorem idealSheaf_eq_of_flat_family {ι : Type*} (V : ι → Scheme.{u})
    (p : ∀ i, V i ⟶ Y) [∀ i, Flat (p i)]
    (hp : ∀ y : Y, ∃ i, ∃ x : V i, p i x = y)
    {I J : Y.IdealSheafData} (h : ∀ i, I.comap (p i) = J.comap (p i)) : I = J := by
  apply idealSheaf_eq_of_stalkIdeal
  intro y
  obtain ⟨i, x, rfl⟩ := hp y
  exact stalkIdeal_eq_of_flat_comap (p i) (h i) x

/-- Faithfully flat pullback is injective on full ideal sheaves. -/
theorem idealSheaf_comap_injective (f : X ⟶ Y) [Flat f] [Surjective f] :
    Function.Injective (fun I : Y.IdealSheafData ↦ I.comap f) := by
  intro I J h
  apply idealSheaf_eq_of_stalkIdeal
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  exact stalkIdeal_eq_of_flat_comap f h x

end FLT.Mazur.FCurve
