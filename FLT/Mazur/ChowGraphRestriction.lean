/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowGraphClosure

/-!
# The Chow graph modification over its common open

Kernels commute with open base change. When the restricted map is a closed
graph, this identifies its source with the restriction of the scheme-theoretic
image. Applied to the Chow graph, this proves that the proper surjective
modification is an isomorphism over exactly the constructed common open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

/-- Kernels of quasi-compact morphisms commute with open base change. -/
lemma ker_openBaseChange {A B C D : Scheme.{u}} (g : A ⟶ B) (g' : C ⟶ D)
    (i : C ⟶ A) (j : D ⟶ B) [QuasiCompact g] [IsOpenImmersion j]
    (H : IsPullback g' i j g) : g.ker.comap j = g'.ker := by
  ext V : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g g' i j H V).symm

/-- If an open base change is closed, its source is the restriction of the
scheme-theoretic image, with the original factorization as comparison map. -/
lemma image_openBaseChange_of_closed {A B D : Scheme.{u}} (g : A ⟶ B)
    (g' : A ⟶ D) (j : D ⟶ B) [QuasiCompact g] [IsOpenImmersion j]
    [IsClosedImmersion g'] (H : IsPullback g' (𝟙 A) j g) :
    IsPullback g' g.toImage j g.imageι := by
  apply isPullback_of_isClosedImmersion
  · simpa using H.w
  · rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    exact ker_openBaseChange g g' (𝟙 A) j H

/-- The scheme-theoretic image after open base change is the pullback of the
original image, obtained by identifying the defining kernel ideals. -/
def imageOpenBaseChangeIso {A B C D : Scheme.{u}} (g : A ⟶ B) (g' : C ⟶ D)
    (i : C ⟶ A) (j : D ⟶ B) [QuasiCompact g] [IsOpenImmersion j]
    (H : IsPullback g' i j g) : g'.image ≅ pullback j g.imageι :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (ker_openBaseChange g g' i j H).symm) ≪≫ g.ker.comapIso j

/-- A graph over an open of the base is closed in the restricted ambient
scheme; its image therefore changes nothing over that same open. -/
lemma image_section_restrict_isIso {X B : Scheme.{u}} (V : X.Opens)
    (g : V.toScheme ⟶ B) (r : B ⟶ X) [QuasiCompact g] [IsSeparated r]
    (h : g ≫ r = V.ι) : IsIso ((g.imageι ≫ r) ∣_ V) := by
  let s : V.toScheme ⟶ pullback r V.ι :=
    pullback.lift g (𝟙 _) (by simpa using h)
  have hs : s ≫ pullback.snd r V.ι = 𝟙 _ := by simp [s]
  have : IsClosedImmersion (s ≫ pullback.snd r V.ι) := by
    rw [hs]
    infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (pullback.snd r V.ι)
  have H : IsPullback s (𝟙 _) (pullback.fst r V.ι) g := by
    apply IsPullback.of_right (h₁₂ := pullback.snd r V.ι)
      (h₂₂ := r) (v₁₃ := V.ι) ?_ (by simp [s])
      (IsPullback.of_hasPullback r V.ι).flip
    rw [hs, h]
    exact IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have Himage := image_openBaseChange_of_closed g s (pullback.fst r V.ι) H
  have Htotal := Himage.paste_horiz (IsPullback.of_hasPullback r V.ι).flip
  rw [hs] at Htotal
  have : IsIso (pullback.snd (g.imageι ≫ r) V.ι) := by
    rw [← Htotal.flip.isoPullback_inv_snd]
    infer_instance
  unfold morphismRestrict
  infer_instance

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The ambient projection to the original source, before taking the graph image. -/
def graphAmbientToSource : graphAmbient f ⟶ X :=
  graphAmbientFst f ≫ (chartData f).sourceClosureι

/-- Separatedness comes from the projective product and the closed source inclusion. -/
instance graphAmbientToSource_isSeparated : IsSeparated (graphAmbientToSource f) := by
  dsimp [graphAmbientToSource]
  infer_instance

/-- The graph of the common-open tuple in the ambient scheme restricted over that open. -/
def graphOverCommon : (chartData f).common.toScheme ⟶
    pullback (graphAmbientToSource f) (chartData f).common.ι :=
  pullback.lift (commonToGraphAmbient f) (𝟙 _) (by
    simp [graphAmbientToSource, ← Category.assoc])

@[reassoc (attr := simp)]
lemma graphOverCommon_snd :
    graphOverCommon f ≫ pullback.snd _ _ = 𝟙 _ := by
  simp [graphOverCommon]

/-- The other graph coordinate is exactly the tuple of projective chart maps. -/
@[reassoc (attr := simp)]
lemma graphOverCommon_toProduct :
    graphOverCommon f ≫ pullback.fst _ _ ≫ graphAmbientSnd f =
      (chartData f).commonToProduct := by
  simp [graphOverCommon, ← Category.assoc]

/-- The restricted graph is closed because its ambient projection is separated. -/
instance graphOverCommon_isClosedImmersion : IsClosedImmersion (graphOverCommon f) := by
  have : IsClosedImmersion (graphOverCommon f ≫ pullback.snd _ _) := by
    rw [graphOverCommon_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd _ _)

/-- The actual modification morphism is an isomorphism over the original common open. -/
instance graphClosureπ_restrict_isIso : IsIso (graphClosureπ f ∣_ (chartData f).common) :=
  image_section_restrict_isIso (chartData f).common (commonToGraphAmbient f)
    (graphAmbientToSource f) (by simp [graphAmbientToSource, ← Category.assoc])

/-- The constructed inverse-image scheme of the common open is that common open. -/
def graphClosureCommonIso :
    (graphClosureπ f ⁻¹ᵁ (chartData f).common).toScheme ≅ (chartData f).common.toScheme :=
  asIso (graphClosureπ f ∣_ (chartData f).common)

@[reassoc (attr := simp)]
lemma graphClosureCommonIso_hom_ι :
    (graphClosureCommonIso f).hom ≫ (chartData f).common.ι =
      (graphClosureπ f ⁻¹ᵁ (chartData f).common).ι ≫ graphClosureπ f :=
  morphismRestrict_ι _ _

/-- Item 16: the canonical graph modification is proper, surjective, and an
isomorphism over exactly the dense common open constructed from `f`. -/
theorem graphClosure_spec :
    IsProper (graphClosureπ f) ∧ Function.Surjective (graphClosureπ f) ∧
      Dense ((chartData f).common : Set X) ∧
      IsIso (graphClosureπ f ∣_ (chartData f).common) :=
  ⟨inferInstance, graphClosureπ_surjective f, (chartData f).common_dense, inferInstance⟩

end FLT.Mazur.Chow
