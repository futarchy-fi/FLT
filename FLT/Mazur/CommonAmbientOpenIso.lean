/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Canonical comparisons of common opens in ambient charts

Open charts containing one common open induce canonical isomorphisms of its
inverse images. These preserve the original ambient map, commute with further
open restriction, and satisfy the cocycle as actual scheme isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.OpenIdealCover

variable {A B C Z : Scheme.{u}}
variable (i : A ⟶ Z) (j : B ⟶ Z) (k : C ⟶ Z)
variable [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k]
variable (U : Z.Opens) (hi : U ≤ i.opensRange) (hj : U ≤ j.opensRange)

omit [IsOpenImmersion i] in
/-- Restricting a chart containing the common open has exactly that open as its image. -/
theorem commonAmbientOpen_range (h : (U : Set Z) ⊆ Set.range i) :
    Set.range ((i ⁻¹ᵁ U).ι ≫ i) = U := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  change i '' (i ⁻¹' (U : Set Z)) = U
  rw [Set.image_preimage_eq_inter_range]
  exact Set.inter_eq_left.mpr h

/-- The two inverse images of a common ambient open are canonically isomorphic. -/
def commonAmbientOpenIso : (i ⁻¹ᵁ U).toScheme ≅ (j ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((i ⁻¹ᵁ U).ι ≫ i) ((j ⁻¹ᵁ U).ι ≫ j)
    ((commonAmbientOpen_range i U hi).trans (commonAmbientOpen_range j U hj).symm)

/-- The comparison preserves the actual map to the original ambient scheme. -/
@[reassoc]
theorem commonAmbientOpenIso_over :
    (commonAmbientOpenIso i j U hi hj).hom ≫ (j ⁻¹ᵁ U).ι ≫ j = (i ⁻¹ᵁ U).ι ≫ i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Comparing a chart with itself on a common open gives the identity. -/
theorem commonAmbientOpenIso_refl : commonAmbientOpenIso i i U hi hi = Iso.refl _ := by
  apply Iso.ext
  apply (cancel_mono ((i ⁻¹ᵁ U).ι ≫ i)).mp
  rw [commonAmbientOpenIso_over, Iso.refl_hom, Category.id_comp]

/-- Three original ambient charts satisfy the cocycle on their common open. -/
theorem commonAmbientOpenIso_trans (hk : U ≤ k.opensRange) :
    commonAmbientOpenIso i j U hi hj ≪≫ commonAmbientOpenIso j k U hj hk =
      commonAmbientOpenIso i k U hi hk := by
  apply Iso.ext
  apply (cancel_mono ((k ⁻¹ᵁ U).ι ≫ k)).mp
  rw [Iso.trans_hom, Category.assoc, commonAmbientOpenIso_over,
    commonAmbientOpenIso_over, commonAmbientOpenIso_over]

/-- Comparing common opens commutes with further open restriction in the original ambient. -/
theorem commonAmbientOpenIso_restrict (V : Z.Opens) (hVU : V ≤ U) :
    A.homOfLE (i.preimage_mono hVU) ≫ (commonAmbientOpenIso i j U hi hj).hom =
      (commonAmbientOpenIso i j V (hVU.trans hi) (hVU.trans hj)).hom ≫
        B.homOfLE (j.preimage_mono hVU) := by
  apply (cancel_mono ((j ⁻¹ᵁ U).ι ≫ j)).mp
  simp only [Category.assoc, commonAmbientOpenIso_over, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.OpenIdealCover
