/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineTripleComparisonCocycle
/-!
# Effective comparisons in geometric affine-test coordinates

The affine coordinate normalization transports effective descent to actual maps of
spectra, and the constructed triple cover proves the resulting geometric cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X}
variable (C C' : Chart p) {A : CommRingCat.{u}}
variable (b : Spec A ⟶ Spec C.baseRing) (b' : Spec A ⟶ Spec C'.baseRing)
variable (w : b ≫ C.base = b' ≫ C'.base)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Effective comparison in the actual geometric coordinates of an affine test. -/
def affineTestComparison : (pullback b).obj (C.sheaf D) ≅
    (pullback b').obj (C'.sheaf D) :=
  ((pullbackCongr (Spec.map_preimage b)).app (C.sheaf D)).symm ≪≫
    (C.commonBaseCrossRefinement C' (Spec.preimage b) (Spec.preimage b')
      (by simpa only [Spec.map_preimage] using w)).effectiveComparison D ≪≫
    (pullbackCongr (Spec.map_preimage b')).app (C'.sheaf D)

private theorem conjugate_cocycle {B : Type*} [Category B]
    {a b c x y z : B} (e : x ≅ a) (f : y ≅ b) (g : z ≅ c)
    (r : x ≅ y) (s : y ≅ z) (t : x ≅ z) (h : r.hom ≫ s.hom = t.hom) :
    (e.symm ≪≫ r ≪≫ f).hom ≫ (f.symm ≪≫ s ≪≫ g).hom =
      (e.symm ≪≫ t ≪≫ g).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc r.hom s.hom, h]

attribute [local irreducible] CrossRefinement.effectiveComparison pullbackCongr sheaf

/-- Comparisons on an arbitrary affine triple test obey the geometric cocycle. -/
theorem affineTestComparison_cocycle (T : Fin 3 → Chart p)
    (a : Spec A ⟶ X) (b : ∀ i, Spec A ⟶ Spec (T i).baseRing)
    (h : ∀ i, b i ≫ (T i).base = a)
    [∀ i, ((pullback (T i).cover).obj M).IsQuasicoherent] :
    (affineTestComparison (T 0) (T 1) (b 0) (b 1) ((h 0).trans (h 1).symm) D).hom ≫
      (affineTestComparison (T 1) (T 2) (b 1) (b 2) ((h 1).trans (h 2).symm) D).hom =
      (affineTestComparison (T 0) (T 2) (b 0) (b 2) ((h 0).trans (h 2).symm) D).hom := by
  unfold affineTestComparison
  exact conjugate_cocycle
    ((pullbackCongr (Spec.map_preimage (b 0))).app ((T 0).sheaf D))
    ((pullbackCongr (Spec.map_preimage (b 1))).app ((T 1).sheaf D))
    ((pullbackCongr (Spec.map_preimage (b 2))).app ((T 2).sheaf D)) _ _ _
    (commonBase_effectiveComparison_cocycle T a (fun i ↦ Spec.preimage (b i))
      (fun i ↦ by simpa only [Spec.map_preimage] using h i) D)

end FLT.Mazur.SchemeAffineDescent.Chart
