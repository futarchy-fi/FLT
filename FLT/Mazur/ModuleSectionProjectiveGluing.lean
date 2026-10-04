/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionProjectiveOverlap
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the projective morphism of a finite generating family

The actual generator opens cover the source. The ratio chart morphisms agree
on their intersections and hence glue to an actual projective-space morphism.
This construction alone does not assert a closed immersion or an O(1) comparison.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} (M : X.Modules) {R : Type u} [CommRing R] (n : ℕ)
    (t : Fin (n + 1) → Γ(M, ⊤))

/-- Restrict a global coefficient map to an actual open. -/
def sectionChartScalars (r : R →+* Γ(X, ⊤)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp r

/-- Scalar restrictions commute with nested open inclusions. -/
lemma sectionChartScalars_restrict (r : R →+* Γ(X, ⊤)) (U V : X.Opens) (hVU : V ≤ U) :
    (X.presheaf.map (homOfLE hVU).op).hom.comp (sectionChartScalars r U) =
      sectionChartScalars r V := by
  ext a
  change X.presheaf.map (homOfLE hVU).op
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (r a)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The local projective map defined on each section's own generator open. -/
def sectionProjectiveLocalMorphism (r : R →+* Γ(X, ⊤)) (i : Fin (n + 1)) :
    (sectionGeneratorOpen M (t i)).toScheme ⟶ ProjectiveSpace.space R (Fin (n + 1)) :=
  sectionProjectiveChartMorphism M n t i (sectionGeneratorOpen M (t i)) le_rfl
    (sectionChartScalars r (sectionGeneratorOpen M (t i)))

/-- The local morphisms agree on the actual open intersections. -/
lemma sectionProjectiveLocalMorphism_inf (r : R →+* Γ(X, ⊤)) (i j : Fin (n + 1)) :
    X.homOfLE (show sectionGeneratorOpen M (t i) ⊓ sectionGeneratorOpen M (t j) ≤
      sectionGeneratorOpen M (t i) from inf_le_left) ≫
        sectionProjectiveLocalMorphism M n t r i =
      X.homOfLE inf_le_right ≫ sectionProjectiveLocalMorphism M n t r j := by
  simp only [sectionProjectiveLocalMorphism, sectionProjectiveChartMorphism_restrict,
    sectionChartScalars_restrict]
  exact sectionProjectiveChartMorphism_change M n t i j _ inf_le_left inf_le_right _

/-- The local morphisms agree on the categorical pullbacks used by scheme gluing. -/
lemma sectionProjectiveLocalMorphism_compatible (r : R →+* Γ(X, ⊤))
    (i j : Fin (n + 1)) :
    pullback.fst (sectionGeneratorOpen M (t i)).ι (sectionGeneratorOpen M (t j)).ι ≫
        sectionProjectiveLocalMorphism M n t r i =
      pullback.snd (sectionGeneratorOpen M (t i)).ι (sectionGeneratorOpen M (t j)).ι ≫
        sectionProjectiveLocalMorphism M n t r j := by
  apply (cancel_epi (isPullback_opens_inf
    (sectionGeneratorOpen M (t i)) (sectionGeneratorOpen M (t j))).isoPullback.hom).mp
  simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd] using sectionProjectiveLocalMorphism_inf M n t r i j

/-- The nonvanishing open cover of a family whose section maps generate locally. -/
def sectionGeneratorCover (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin (n + 1))
    (fun i ↦ (sectionGeneratorOpen M (t i)).toScheme)
    (fun i ↦ (sectionGeneratorOpen M (t i)).ι)
    (fun x ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show x ∈ ⨆ i, sectionGeneratorOpen M (t i) by rw [ht]; trivial)
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
    (fun _ ↦ inferInstance)

/-- The projective-space morphism of the actual finite generating family. -/
def sectionProjectiveMorphism (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤)
    (r : R →+* Γ(X, ⊤)) : X ⟶ ProjectiveSpace.space R (Fin (n + 1)) :=
  (sectionGeneratorCover M n t ht).glueMorphisms
    (sectionProjectiveLocalMorphism M n t r) (sectionProjectiveLocalMorphism_compatible M n t r)

/-- The glued morphism restricts to the actual ratio morphism on every generator open. -/
@[reassoc] lemma sectionGeneratorOpen_ι_projectiveMorphism
    (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤)
    (r : R →+* Γ(X, ⊤)) (i : Fin (n + 1)) :
    (sectionGeneratorOpen M (t i)).ι ≫ sectionProjectiveMorphism M n t ht r =
      sectionProjectiveLocalMorphism M n t r i :=
  (sectionGeneratorCover M n t ht).ι_glueMorphisms _ _ i

/-- The glued morphism pulls each standard chart back to its actual generator open. -/
lemma sectionProjectiveMorphism_preimage_chart
    (ht : ⨆ i, sectionGeneratorOpen M (t i) = ⊤)
    (r : R →+* Γ(X, ⊤)) (j : Fin (n + 1)) :
    sectionProjectiveMorphism M n t ht r ⁻¹ᵁ ProjectiveSpace.chart R (Fin (n + 1)) j =
      sectionGeneratorOpen M (t j) := by
  have hlocal (i : Fin (n + 1)) : sectionGeneratorOpen M (t i) ⊓
      (sectionProjectiveMorphism M n t ht r ⁻¹ᵁ
        ProjectiveSpace.chart R (Fin (n + 1)) j) =
      sectionGeneratorOpen M (t i) ⊓ sectionGeneratorOpen M (t j) := by
    rw [← Scheme.Opens.opensRange_ι (sectionGeneratorOpen M (t i)),
      ← Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.comp_preimage,
      sectionGeneratorOpen_ι_projectiveMorphism]
    simpa only [sectionProjectiveLocalMorphism, Scheme.Opens.opensRange_ι] using
      sectionProjectiveChartMorphism_preimage_image M n t i _ le_rfl
        (sectionChartScalars r (sectionGeneratorOpen M (t i))) j
  apply SetLike.ext
  intro x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, sectionGeneratorOpen M (t i) by rw [ht]; trivial)
  constructor
  · intro hx
    exact (show x ∈ sectionGeneratorOpen M (t i) ⊓ sectionGeneratorOpen M (t j) from
      (hlocal i) ▸ ⟨hi, hx⟩).2
  · intro hx
    exact (show x ∈ sectionGeneratorOpen M (t i) ⊓
      (sectionProjectiveMorphism M n t ht r ⁻¹ᵁ
        ProjectiveSpace.chart R (Fin (n + 1)) j) from (hlocal i).symm ▸ ⟨hi, hx⟩).2

end FLT.Mazur.FCurve
