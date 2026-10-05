/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGradedProjChartBaseChange

/-!
# Proj commutes with flat scalar extension

The standard homogeneous-localization comparisons are Cartesian, and their
open-cover gluing gives the actual base-change square of schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open scoped TensorProduct FLT.Mazur.HomogeneousLocalizationScalars
universe u
namespace FLT.Mazur.FlatGradedProjBaseChange
open GradedProjBaseChangeMap GradedProjStructuralMap FlatGradedProjChartBaseChange
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A standard affine chart of the original Proj pulls back to its extended standard chart. -/
lemma chart_isPullback {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    IsPullback (Proj.awayι (baseGrade (B := B) 𝒜) (inclusion 𝒜 f)
        ((inclusion 𝒜).map_mem hf) hd)
      (Spec.map (CommRingCat.ofHom (Away.map (inclusion (B := B) 𝒜) f)))
      (projection (B := B) 𝒜) (Proj.awayι 𝒜 f hf hd) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact awayι_projection 𝒜 hd f hf
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι, projection_preimage_basicOpen]
    rfl

/-- The actual Proj square for flat scalar extension is Cartesian. -/
lemma isPullback [Module.Flat R B] :
    IsPullback (projection (B := B) 𝒜) (toSpecBase (baseGrade (B := B) 𝒜))
      (toSpecBase 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover 𝒜).openCover
  intro s
  have h := chart_isPullback (B := B) 𝒜 s.2.2 s.1.2
  have ha := isPullback_away (B := B) 𝒜 s.2.2
  have ha' : IsPullback
      (Spec.map (CommRingCat.ofHom (Away.map (inclusion (B := B) 𝒜) (s.2 : A))))
      (Proj.awayι (baseGrade (B := B) 𝒜) (inclusion (B := B) 𝒜 (s.2 : A))
        ((inclusion 𝒜).map_mem s.2.2) s.1.2 ≫ toSpecBase (baseGrade (B := B) 𝒜))
      (Proj.awayι 𝒜 (s.2 : A) s.2.2 s.1.2 ≫ toSpecBase 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    simpa only [awayι_toSpecBase] using ha
  refine ha'.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · change _ ≫ 𝟙 _ = h.isoPullback.hom ≫ pullback.snd _ _
    rw [Category.comp_id, h.isoPullback_hom_snd]
  · change (_ ≫ toSpecBase (baseGrade (B := B) 𝒜)) ≫ 𝟙 _ =
      h.isoPullback.hom ≫ pullback.fst _ _ ≫ toSpecBase (baseGrade (B := B) 𝒜)
    rw [Category.comp_id, ← Category.assoc, h.isoPullback_hom_fst]

end FLT.Mazur.FlatGradedProjBaseChange
