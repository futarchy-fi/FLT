/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardCoproductSection

/-!
# Component pullbacks of relative disjoint unions

A componentwise map of scheme coproducts pulls each target component back to
exactly its source component. This also applies to maps meeting many components.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {ι : Type u} {S : Scheme.{u}} (A B : ι → Over S)

/-- The relative morphism assembled from a family of actual component morphisms. -/
def relativeCoproductMap (a : ∀ i, A i ⟶ B i) :
    relativeCoproductTest A ⟶ relativeCoproductTest B :=
  Over.homMk (Sigma.desc (fun i ↦ (a i).left ≫ Sigma.ι (fun j ↦ (B j).left) i)) (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι _ i ≫ Sigma.desc _ ≫ Sigma.desc _ = Sigma.ι _ i ≫ Sigma.desc _
    simp only [Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc]
    exact Over.w (a i))

/-- Each component retains its original map. -/
theorem relativeCoproductArrow_map (a : ∀ i, A i ⟶ B i) (i : ι) :
    relativeCoproductArrow A i ≫ relativeCoproductMap A B a =
      a i ≫ relativeCoproductArrow B i :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

/-- Pulling back a target component of a disjoint union gives the source component. -/
theorem relativeCoproductMap_component_isPullback (a : ∀ i, A i ⟶ B i) (i : ι) :
    IsPullback (a i) (relativeCoproductArrow A i) (relativeCoproductArrow B i)
      (relativeCoproductMap A B a) := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  change IsPullback (a i).left (Sigma.ι (fun j ↦ (A j).left) i)
    (Sigma.ι (fun j ↦ (B j).left) i) (relativeCoproductMap A B a).left
  refine IsOpenImmersion.isPullback _ _ _ _
    (congrArg (fun z ↦ z.left) (relativeCoproductArrow_map A B a i)) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨⟨j, z⟩, rfl⟩ := (sigmaMk (fun i ↦ (A i).left)).surjective x
    rw [sigmaMk_mk] at *
    change Sigma.ι (fun i ↦ (B i).left) i y =
      (Sigma.ι (fun i ↦ (A i).left) j ≫
        Sigma.desc (fun i ↦ (a i).left ≫ Sigma.ι (fun j ↦ (B j).left) i)) z at hxy
    rw [Sigma.ι_comp_desc, Scheme.Hom.comp_apply] at hxy
    have hij : i = j := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hxy)
    subst j
    exact ⟨z, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨(a i).left x, ?_⟩
    change _ = (Sigma.ι (fun i ↦ (A i).left) i ≫
      Sigma.desc (fun i ↦ (a i).left ≫ Sigma.ι (fun j ↦ (B j).left) i)) x
    rw [Sigma.ι_comp_desc, Scheme.Hom.comp_apply]

end FLT.Mazur.SchemePicard
