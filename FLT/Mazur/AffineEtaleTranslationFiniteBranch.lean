/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleTranslationFiniteNeighborhood
public import FLT.Mazur.AffineBaseSectionFunctor

/-!
# Finite branches of actual affine etale translations

Every point of an affine etale translation has an affine etale neighborhood
finite over a constructed etale base. The structural square is the original
one. The coefficient change retains finite type over the integers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EtaleTranslationBranch
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {V : Scheme.{u}}
  (g : V ⟶ Spec (.of R)) [IsAffine V] [Etale g]

/-- The actual coefficient algebra of an affine etale translation is etale. -/
theorem sectionAlgebra_etale :
    let _ := affineBaseSectionAlgebra g
    Algebra.Etale R Γ(V, ⊤) := by
  let _ := affineBaseSectionAlgebra g
  let _ : IsAffine (Over.mk g).left := ‹IsAffine V›
  have h : V.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))) = g :=
    affineBaseSectionsSpecIso_over R (Over.mk g)
  have hh : Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))) =
      V.isoSpec.inv ≫ g := by rw [← h, Iso.inv_hom_id_assoc]
  apply RingHom.etale_algebraMap.mp
  apply (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap R Γ(V, ⊤)))).mp
  rw [hh]
  infer_instance

/-- Construct a genuine finite etale branch through any original affine translation point. -/
theorem exists_affine_finite_etale_neighborhood (v : V) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S)
      (W : Scheme.{u}) (_ : IsAffine W) (a : W ⟶ V) (t : W ⟶ Spec (.of S)),
      Etale a ∧ Etale t ∧ IsFinite t ∧
      a ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) ∧
      ∃ w : W, a w = v ∧ ∀ z : W, t z = t w → z = w := by
  let _ := affineBaseSectionAlgebra g
  let _ : IsAffine (Over.mk g).left := ‹IsAffine V›
  let _ := sectionAlgebra_etale g
  obtain ⟨S, hS, hRS, hEt, e, _, hfin, ht, ha, x, hx, huniq⟩ :=
    exists_finite_etale_branch (R := R) (V.isoSpec.hom v)
  let a := toOriginal e ≫ V.isoSpec.inv
  have h : V.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))) = g :=
    affineBaseSectionsSpecIso_over R (Over.mk g)
  refine ⟨S, hS, hRS, hEt, source e, inferInstance, a, toBase e,
    inferInstance, ht, hfin, ?_, x, ?_, huniq⟩
  · dsimp only [a]
    rw [Category.assoc, ← h, Iso.inv_hom_id_assoc]
    exact base_square e
  · change V.isoSpec.inv (toOriginal e x) = v
    rw [hx]
    exact congrArg (fun j : V ⟶ V ↦ j v) V.isoSpec.hom_inv_id

/-- Etale coefficient refinements preserve the integer finite-type hypothesis of Hilbert charts. -/
theorem finiteType_integer_base {S : Type u} [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Algebra.FiniteType ℤ R] : Algebra.FiniteType ℤ S :=
  Algebra.FiniteType.trans (R := ℤ) (S := R) inferInstance inferInstance

end FLT.Mazur.EtaleTranslationBranch
