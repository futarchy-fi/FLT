/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonIdealDirectSum

/-!
# Generic injectivity of the constructed ideal sum

Sections of the structure sheaf on an integral scheme inject into the function
field. This detects zero maps into finite free sheaves and their ideal sums,
so generic injectivity gives an actual monomorphism. Closed pushforward then
constructs the coherent cokernel sequence in Stacks 30.12.2 (01YE).
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericCoordinates FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.CommonIdealDirectSum FLT.Mazur.AnnihilatorSubsheaf
open FLT.Mazur.CoherentGenericIdealEmbedding

universe u

namespace FLT.Mazur.GenericIdealInjection

variable {X : Scheme.{u}}

/-- The generic stalk detects zero morphisms into the structure module. -/
theorem structure_map_eq_zero [IsIntegral X] {M : X.Modules}
    (f : M ⟶ structureModule X) (h : (stalk (genericPoint X)).map f = 0) : f = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change f.app U s = 0
  apply TopCat.Presheaf.section_ext
    (⟨(structureModule X).presheaf, (structureModule X).isSheaf⟩ : TopCat.Sheaf Ab X)
  intro x hx
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  have hz : (structureModule X).presheaf.germ U (genericPoint X) hη (f.app U s) = 0 := by
    erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U (genericPoint X) hη f.mapPresheaf]
    change (stalk (genericPoint X)).map f _ = 0
    rw [h]
    rfl
  have hs : f.app U s = 0 := by
    apply germ_injective_of_isIntegral X (genericPoint X) hη
    rw [map_zero, ← structureStalkIso_germ]
    rw [hz, map_zero]
  rw [hs]

/-- A finite free target inherits generic detection coordinate by coordinate. -/
theorem free_map_eq_zero [IsIntegral X] {M : X.Modules} (r : ℕ)
    (f : M ⟶ finiteFree X r) (h : (stalk (genericPoint X)).map f = 0) : f = 0 := by
  apply (cancel_mono (finiteFreeProductIso X r).hom).mp
  apply Pi.hom_ext
  intro i
  rw [zero_comp, zero_comp]
  apply structure_map_eq_zero
  simp only [Functor.map_comp, h, zero_comp]

/-- The actual ideal-sum inclusion transfers generic detection from the finite free target. -/
theorem idealSum_map_eq_zero [IsIntegral X] {M : X.Modules} (I : X.IdealSheafData)
    (r : ℕ) (f : M ⟶ idealSum I r) (h : (stalk (genericPoint X)).map f = 0) : f = 0 := by
  apply (cancel_mono (sumInclusion I r)).mp
  rw [zero_comp]
  apply free_map_eq_zero r
  simp only [Functor.map_comp, h, zero_comp]

/-- Generic injectivity on an ideal direct sum is global injectivity. -/
theorem mono_of_generic_mono [IsIntegral X] (I : X.IdealSheafData) (r : ℕ)
    {G : X.Modules} (f : idealSum I r ⟶ G) [Mono ((stalk (genericPoint X)).map f)] :
    Mono f := by
  apply Preadditive.mono_of_cancel_zero
  intro M a ha
  apply idealSum_map_eq_zero I r a
  apply (cancel_mono ((stalk (genericPoint X)).map f)).mp
  rw [zero_comp, ← Functor.map_comp, ha, Functor.map_zero]

/-- An invertible restriction gives an invertible stalk at every point of the open. -/
lemma stalk_isIso_of_restrict {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    [IsIso ((restrictFunctor U.ι).map f)] (x : X) (hx : x ∈ U) :
    IsIso ((stalk x).map f) :=
  (NatIso.isIso_map_iff (restrictStalkNatIso U.ι ⟨x, hx⟩) f).mp
    (inferInstanceAs (IsIso ((stalk (⟨x, hx⟩ : U.toScheme)).map
      ((restrictFunctor U.ι).map f))))

/-- Finite sums of actual ideal modules are coherent, using their ideal-action image. -/
instance idealSum_coherent [IsLocallyNoetherian X] (I : X.IdealSheafData) (r : ℕ) :
    (idealSum I r).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (multipleSumIso I r) inferInstance

/-- The finite ideal sum stays coherent after an actual closed pushforward. -/
instance closedIdealSum_coherent [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (I : J.subscheme.IdealSheafData) (r : ℕ) :
    ((pushforward J.subschemeι).obj (idealSum I r)).IsFinitePresentation := by
  have := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  exact closedPushforward_isFinitePresentation J.subschemeι (idealSum I r)

/-- The chosen ideal sum embeds into a coherent sheaf and gives its actual cokernel sequence. -/
theorem exists_generic_embedding [IsNoetherian X] [IsIntegral X]
    (G : X.Modules) [G.IsFinitePresentation] :
    ∃ (I : X.IdealSheafData), I ≠ ⊥ ∧ ∃ f :
      idealSum I (Module.finrank X.functionField (G.presheaf.stalk (genericPoint X))) ⟶ G,
      Mono f ∧ IsIso ((stalk (genericPoint X)).map f) ∧
        CoherentSequence (ShortComplex.cokernelSequence f) := by
  obtain ⟨U, hx, n, hI, f, hf⟩ := exists_common_ideal G
  have := stalk_isIso_of_restrict f U _ hx
  have := mono_of_generic_mono (comparisonIdeal U ^ n) _ f
  exact ⟨_, hI, f, inferInstance, inferInstance, coherent_cokernelSequence f⟩

/-- The ambient embedding is the actual pushforward followed by the constructed A3 inclusion. -/
def ambientMap [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] {I : J.subscheme.IdealSheafData} {r : ℕ}
    (f : idealSum I r ⟶ CoherentClosedReduction.descent J F) :
    (pushforward J.subschemeι).obj (idealSum I r) ⟶ F :=
  (pushforward J.subschemeι).map f ≫ CoherentClosedReduction.embedding J F

/-- The resulting ambient comparison is monic whenever the constructed map on the subscheme is. -/
instance ambientMap_mono [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] {I : J.subscheme.IdealSheafData} {r : ℕ}
    (f : idealSum I r ⟶ CoherentClosedReduction.descent J F) [Mono f] :
    Mono (ambientMap J F f) := by dsimp only [ambientMap]; infer_instance

/-- At the closed generic point the composite retains the entire original stalk. -/
lemma ambientMap_stalk_isIso [IsLocallyNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (F : X.Modules) [F.IsFinitePresentation]
    (hF : StalkAnnihilated F (J.subschemeι (genericPoint J.subscheme)))
    {I : J.subscheme.IdealSheafData} {r : ℕ}
    (f : idealSum I r ⟶ CoherentClosedReduction.descent J F)
    [IsIso ((stalk (genericPoint J.subscheme)).map f)] :
    IsIso ((stalk (J.subschemeι (genericPoint J.subscheme))).map (ambientMap J F f)) := by
  have := closed_map_stalk_isIso J.subschemeι f (genericPoint J.subscheme)
  have he : IsIso ((stalk (J.subschemeι (genericPoint J.subscheme))).map
      (CoherentClosedReduction.embedding J F)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun m ↦ (stalk (J.subschemeι (genericPoint J.subscheme))).map
      (CoherentClosedReduction.embedding J F) m)
    simp_rw [← CoherentClosedReduction.embeddingStalkEquiv_apply J F hF]
    exact (CoherentClosedReduction.embeddingStalkEquiv J F hF).bijective
  dsimp only [ambientMap]
  rw [Functor.map_comp]
  infer_instance

/-- Stacks 01YE: the common ideal on the integral closed subscheme gives a coherent sequence. -/
theorem exists_closed_ideal_embedding [IsNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (F : X.Modules) [F.IsFinitePresentation]
    (hF : StalkAnnihilated F (J.subschemeι (genericPoint J.subscheme))) :
    ∃ (I : J.subscheme.IdealSheafData), I ≠ ⊥ ∧ ∃ f :
      (pushforward J.subschemeι).obj (idealSum I
        (Module.finrank J.subscheme.functionField
          ((CoherentClosedReduction.descent J F).presheaf.stalk (genericPoint J.subscheme)))) ⟶ F,
      Mono f ∧ IsIso ((stalk (J.subschemeι (genericPoint J.subscheme))).map f) ∧
        CoherentSequence (ShortComplex.cokernelSequence f) := by
  have := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have : NoetherianSpace J.subscheme :=
    J.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian J.subscheme := ⟨⟩
  obtain ⟨I, hI, f, hf, hη, _⟩ := exists_generic_embedding (CoherentClosedReduction.descent J F)
  have := ambientMap_stalk_isIso J F hF f
  exact ⟨I, hI, ambientMap J F f, inferInstance, inferInstance,
    coherent_cokernelSequence (ambientMap J F f)⟩

end FLT.Mazur.GenericIdealInjection
