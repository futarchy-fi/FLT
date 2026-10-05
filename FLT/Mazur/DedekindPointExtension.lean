/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperSectionGluing
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Proper points over Dedekind domains

Stalks of the spectrum of a Dedekind domain are valuation rings (including
its generic field). Thus the local extensions glue. The fraction field may be
any specified fraction field, rather than only the scheme's function field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace FLT.Mazur

set_option backward.isDefEq.respectTransparency false in
/-- Every stalk of the spectrum of a Dedekind domain is a valuation ring. -/
theorem dedekindSpec_stalk_valuationRing (R : CommRingCat.{u}) [IsDedekindDomain R]
    (s : Spec R) : ValuationRing ((Spec R).presheaf.stalk s) := by
  let : Algebra R ((Spec R).presheaf.stalk s) :=
    (StructureSheaf.toStalk R s).hom.toAlgebra
  let : IsLocalization.AtPrime ((Spec R).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R s
  let hD : IsDedekindDomain ((Spec R).presheaf.stalk s) :=
    IsLocalization.AtPrime.isDedekindDomain R s.asIdeal _
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    ((Spec R).presheaf.stalk s)).out 3 2).mp hD

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A proper scheme over a Dedekind domain has a unique section extending each
point over its specified fraction field. -/
theorem Sections.existsUnique_of_dedekind (R : CommRingCat.{u}) [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Spec R)) [IsProper X.hom]
    (x : Points X (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    ∃! y : Sections X,
      Sections.restrict (Spec.map (CommRingCat.ofHom (algebraMap R K))) y = x := by
  let S := Spec R
  let : ∀ s : S, ValuationRing (S.presheaf.stalk s) := dedekindSpec_stalk_valuationRing R
  let F := S.functionField
  let e : K ≃ₐ[R] F := IsLocalization.algEquiv R⁰ K F
  let a : Spec (.of F) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom e.toRingHom)
  let : IsIso a := by
    let : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
    dsimp only [a]
    infer_instance
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      S.fromSpecStalk (genericPoint S) := by
    rw [Spec.fromSpecStalk_eq']
    dsimp only [a]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact e.toAlgHom.comp_algebraMap
  let x' : Points X (S.fromSpecStalk (genericPoint S)) :=
    Over.homMk (a ≫ x.left) (by rw [Category.assoc, Over.w x]; exact ha)
  obtain ⟨y, hy, huniq⟩ := Sections.existsUnique_of_valuation_stalks S X x'
  have hy' : Sections.restrict (Spec.map (CommRingCat.ofHom (algebraMap R K))) y = x := by
    apply Over.OverMorphism.ext
    apply (cancel_epi a).mp
    change a ≫ (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ y.left) = a ≫ x.left
    rw [← Category.assoc, ha]
    exact congrArg (fun z => z.left) hy
  refine ⟨y, hy', ?_⟩
  intro z hz
  apply huniq
  apply Over.OverMorphism.ext
  change S.fromSpecStalk (genericPoint S) ≫ z.left = a ≫ x.left
  rw [← ha, Category.assoc]
  exact congrArg (fun t => a ≫ t.left) hz

end FLT.Mazur
