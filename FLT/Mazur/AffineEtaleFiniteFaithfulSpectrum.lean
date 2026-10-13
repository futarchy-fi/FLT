/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFiniteFaithfulRefinement

/-!
# Finite faithful refinements with actual coefficient spectra

The already constructed finite faithful affine bases are identified with
the spectra of their section rings. Their etale coefficient algebras are
of finite type over the integers, as required by the proper-family charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EtaleTranslationBranch
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R] {V : Scheme.{u}}
  (g : V ⟶ Spec (.of R)) [IsAffine V] [Etale g]

/-- The finite faithful branch construction supplies a genuine finite-type coefficient spectrum. -/
theorem exists_finite_faithful_spectrum (v : V) (U : V.Opens) (hv : v ∈ U) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S)
      (_ : Algebra.FiniteType ℤ S) (W : Scheme.{u}) (_ : IsAffine W)
      (a : W ⟶ V) (t : W ⟶ Spec (.of S)),
      Etale a ∧ Etale t ∧ IsFinite t ∧ Surjective t ∧
      a ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) ∧
      Set.range a ⊆ U ∧ ∃ w : W, a w = v := by
  obtain ⟨T, W, hT, hW, b, a, t, hb, ha, ht, hfin, hsurj, hsq, hU, hw⟩ :=
    exists_finite_faithful_refinement g v U hv
  let _ := affineBaseSectionAlgebra b
  let _ := sectionAlgebra_etale b
  let _ : Algebra.FiniteType ℤ Γ(T, ⊤) := finiteType_integer_base (R := R)
  let _ : IsAffine (Over.mk b).left := hT
  have h : T.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, ⊤))) = b :=
    affineBaseSectionsSpecIso_over R (Over.mk b)
  refine ⟨Γ(T, ⊤), inferInstance, inferInstance, inferInstance, inferInstance,
    W, hW, a, t ≫ T.isoSpec.hom, ha, inferInstance, inferInstance, inferInstance,
    ?_, hU, hw⟩
  rw [Category.assoc, h]
  exact hsq

end FLT.Mazur.EtaleTranslationBranch
