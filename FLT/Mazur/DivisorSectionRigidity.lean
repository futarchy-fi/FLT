/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection

/-!
# Rigidity of a divisor line with its canonical section

Endomorphisms of an effective divisor line are determined by the canonical
section. The proof cancels the regular equation in each Cartier chart; it
does not treat the canonical section as a categorical epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.FCurve

/-- On a free rank-one module, a regular-coordinate vector determines an endomorphism. -/
theorem rankOne_end_ext_of_regular {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) (s : M) (hs : IsRegular (e s)) (f g : M →ₗ[R] M)
    (h : f s = g s) : f = g := by
  have hc (x : M) : x = e x • e.symm 1 := by
    apply e.injective
    simp
  have hb : f (e.symm 1) = g (e.symm 1) := by
    apply e.injective
    apply hs.1
    have hh := congrArg e h
    conv_lhs at hh => rw [hc s, _root_.map_smul, _root_.map_smul]
    conv_rhs at hh => rw [hc s, _root_.map_smul, _root_.map_smul]
    exact hh
  ext x
  rw [hc x, _root_.map_smul, _root_.map_smul, hb]

variable {X : Scheme} {I : X.IdealSheafData}

/-- On each Cartier chart the canonical section determines all line endomorphisms. -/
theorem divisorLine_end_ext_chart (hI : EffectiveCartier I) {U : X.affineOpens}
    (hU : CartierChart I U) (f g : divisorLineBundle I hI ⟶ divisorLineBundle I hI)
    (h : divisorSectionMap hI ≫ f = divisorSectionMap hI ≫ g) : f.app U.1 = g.app U.1 := by
  suffices hh : (f.val.app (op U.1)).hom = (g.val.app (op U.1)).hom by
    ext s
    exact DFunLike.congr_fun hh s
  apply rankOne_end_ext_of_regular
    ((hU.divisorSectionsEquiv hI).trans hU.dualEquiv) (divisorSection hI U.1)
  · change IsRegular (hU.dualEquiv (divisorChartEval I U (divisorSection hI U.1)))
    rw [divisorSection_coordinate]
    exact hU.choose_spec.1
  · exact congrArg (fun k ↦ k.app U.1 (1 : Γ(X, U))) h

/-- The canonical section determines an endomorphism of the entire effective divisor line. -/
theorem divisorLine_end_ext (hI : EffectiveCartier I)
    (f g : divisorLineBundle I hI ⟶ divisorLineBundle I hI)
    (h : divisorSectionMap hI ≫ f = divisorSectionMap hI ≫ g) : f = g := by
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext (divisorLineBundle I hI).isSheaf
  intro x hx
  obtain ⟨V, hxV, hVU, hV⟩ := hI.exists_chart_le hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  have hf := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE hVU).op) s
  have hg := ConcreteCategory.congr_hom (g.mapPresheaf.naturality (homOfLE hVU).op) s
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hf hg
  rw [← hf, ← hg]
  exact ConcreteCategory.congr_hom (divisorLine_end_ext_chart hI hV f g h) _

/-- Isomorphisms to a divisor line coincide if they carry a specified section to its section. -/
theorem divisorLine_iso_ext {L : X.Modules} (hI : EffectiveCartier I)
    (s : structureModule X ⟶ L) (e e' : L ≅ divisorLineBundle I hI)
    (he : s ≫ e.hom = divisorSectionMap hI)
    (he' : s ≫ e'.hom = divisorSectionMap hI) : e = e' := by
  have hh : e.inv ≫ e'.hom = 𝟙 _ := by
    apply divisorLine_end_ext hI
    rw [← he, Category.assoc, Iso.hom_inv_id_assoc, he', Category.comp_id]
    exact he.symm
  apply Iso.ext
  rw [← cancel_epi e.inv, Iso.inv_hom_id]
  exact hh.symm

end FLT.Mazur.FCurve
