/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealFppfEffectiveDescent
public import FLT.Mazur.CartierIdealCoproduct
public import FLT.Mazur.SchemeFppfFamilyOverlapCover

/-!
# Effective full Cartier ideal descent for arbitrary fppf covering families

Glue the original ideals on the disjoint-union open cover, then descend along
its fppf projection. The original pairwise matching proves equality on the
total double overlap. Every component ideal is recovered exactly.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemeFppfFamily
variable {X : Scheme.{0}} (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage X)
  (I : ∀ i, (𝒰.X i).IdealSheafData) (hI : ∀ i, EffectiveCartier (I i))
  (h : ∀ i j, (I i).comap (pullback.fst (𝒰.f i) (𝒰.f j)) =
    (I j).comap (pullback.snd (𝒰.f i) (𝒰.f j)))

include h in
/-- Pairwise matching of the supplied ideals implies full matching on the coproduct overlap. -/
lemma coproductIdeal_fppf_matching :
    (coproductIdeal 𝒰.X I).comap (pullback.fst (projection 𝒰) (projection 𝒰)) =
      (coproductIdeal 𝒰.X I).comap (pullback.snd (projection 𝒰) (projection 𝒰)) := by
  apply idealSheaf_eq_of_flat_family (pair 𝒰) (pairMap 𝒰)
    (fun x ↦ (pairCover 𝒰).exists_eq x)
  intro ij
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    pairMap_fst, pairMap_snd, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp, coproductIdeal_comap, coproductIdeal_comap]
  exact h ij.1 ij.2

/-- The actual global full ideal obtained from the original covering-family ideals. -/
def cartierIdealFamilyDescended : X.IdealSheafData :=
  cartierIdealDescended (projection 𝒰) (coproductIdeal 𝒰.X I)
    (coproductIdeal_cartier 𝒰.X I hI) (coproductIdeal_fppf_matching 𝒰 I h)

/-- The descended full ideal is Cartier without any finiteness assumption on the family. -/
theorem cartierIdealFamilyDescended_cartier :
    EffectiveCartier (cartierIdealFamilyDescended 𝒰 I hI h) :=
  cartierIdealDescended_cartier _ _ _ _

/-- The global ideal recovers every original full component ideal. -/
lemma cartierIdealFamilyDescended_comap (i : 𝒰.I₀) :
    (cartierIdealFamilyDescended 𝒰 I hI h).comap (𝒰.f i) = I i := by
  rw [← inclusion_projection 𝒰 i, Scheme.IdealSheafData.comap_comp]
  change ((cartierIdealDescended _ _ _ _).comap (projection 𝒰)).comap _ = _
  rw [cartierIdealDescended_comap, coproductIdeal_comap]

include hI h in
/-- Any compatible full Cartier family has exactly one full global Cartier ideal. -/
theorem existsUnique_cartierIdeal_family_descent :
    ∃! J : X.IdealSheafData, EffectiveCartier J ∧ ∀ i, J.comap (𝒰.f i) = I i := by
  refine ⟨cartierIdealFamilyDescended 𝒰 I hI h,
    ⟨cartierIdealFamilyDescended_cartier 𝒰 I hI h,
      cartierIdealFamilyDescended_comap 𝒰 I hI h⟩, ?_⟩
  intro J hJ
  let V : X.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  let _ (i : 𝒰.I₀) : Flat (𝒰.f i) :=
    (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).1
  apply idealSheaf_eq_of_flat_family 𝒰.X 𝒰.f (fun x ↦ V.exists_eq x)
  intro i
  exact (hJ.2 i).trans (cartierIdealFamilyDescended_comap 𝒰 I hI h i).symm

end FLT.Mazur.FCurve
