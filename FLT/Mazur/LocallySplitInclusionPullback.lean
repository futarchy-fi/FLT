/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackRestrictionPasting
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Arbitrary pullback of locally split inclusions

An inclusion split on an open cover remains split on the inverse-image cover.
Cancellation on that cover proves monicity after arbitrary base change,
without a flatness hypothesis on the test morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallySplitInclusionPullback
open FCurve ModuleSheafMorphismGluing
variable {X T : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N) (f : T ⟶ X)

/-- The genuine open pullback comparison preserves the original ambient morphism. -/
lemma open_naturality (U : X.Opens) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map a) ≫
        (modulePullbackOpenIso f U N).hom =
      (modulePullbackOpenIso f U M).hom ≫
        (pullback (f ∣_ U)).map ((restrictFunctor U.ι).map a) :=
  modulePullbackRestrictIso_naturality f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm a

/-- A local retraction pulls back through the actual geometric restriction comparisons. -/
def openSplit (U : X.Opens) [IsSplitMono ((restrictFunctor U.ι).map a)] :
    SplitMono ((restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map a)) where
  retraction := (modulePullbackOpenIso f U N).hom ≫
    (pullback (f ∣_ U)).map (CategoryTheory.retraction ((restrictFunctor U.ι).map a)) ≫
      (modulePullbackOpenIso f U M).inv
  id := by
    rw [← Category.assoc, ← Category.assoc, open_naturality]
    simp only [Category.assoc, ← Functor.map_comp, IsSplitMono.id]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]

instance (U : X.Opens) [IsSplitMono ((restrictFunctor U.ι).map a)] :
    IsSplitMono ((restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map a)) :=
  IsSplitMono.mk' (openSplit a f U)

/-- A jointly covering family of local splittings makes every test pullback monic. -/
theorem mono_of_split_cover {I : Type v} (U : I → X.Opens) (hU : iSup U = ⊤)
    [∀ i, IsSplitMono ((restrictFunctor (U i).ι).map a)] : Mono ((pullback f).map a) := by
  have hcover : iSup (fun i ↦ f ⁻¹ᵁ U i) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f x ∈ iSup U by rw [hU]; trivial)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  refine ⟨fun {Z} b c h ↦ ?_⟩
  apply hom_ext_restrict (fun i ↦ f ⁻¹ᵁ U i) hcover
  intro i
  apply (cancel_mono ((restrictFunctor (f ⁻¹ᵁ U i).ι).map ((pullback f).map a))).mp
  rw [← Functor.map_comp, ← Functor.map_comp, h]

end FLT.Mazur.LocallySplitInclusionPullback
