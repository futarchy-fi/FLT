/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AnnihilatorStalk
public import FLT.Mazur.CoherentGenericIdealEmbedding
public import FLT.Mazur.GlobalClosedModuleDescent
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Reduction to an integral closed subscheme

The canonical annihilator subsheaf descends to the closed subscheme. At its
integral generic point the original maximal-ideal annihilation hypothesis makes
the constructed inclusion an isomorphism on stalks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.CoherentClosedReduction

open AnnihilatorSubsheaf CoherentGenericIdealEmbedding

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- On an integral closed subscheme, the actual ideal stalk is the stalk-map kernel. -/
theorem stalkIdeal_eq_ker [IsIntegral I.subscheme] (z : I.subscheme) :
    stalkIdeal I (I.subschemeι z) = RingHom.ker (I.subschemeι.stalkMap z).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hz, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show I.subschemeι z ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  apply le_antisymm
  · rw [stalkIdeal_eq_map I _ ⟨U, hU⟩ hz, Ideal.map_le_iff_le_comap]
    intro a ha
    change I.subschemeι.stalkMap z (X.presheaf.germ U _ hz a) = 0
    rw [Scheme.Hom.germ_stalkMap_apply]
    have ha' : I.subschemeι.app U a = 0 := by
      exact (I.ker_subschemeι_app ⟨U, hU⟩ ▸ ha :
        a ∈ RingHom.ker (I.subschemeι.app U).hom)
    rw [ha', map_zero]
  · intro r hr
    obtain ⟨V, hx, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    let b := X.presheaf.map (homOfLE hWV).op a
    have hb : X.presheaf.germ W _ hxW b = X.presheaf.germ V _ hx a :=
      X.presheaf.germ_res_apply (homOfLE hWV) _ hxW a
    have hz0 : I.subschemeι.app W b = 0 := by
      apply germ_injective_of_isIntegral I.subscheme z hxW
      rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply, hb]
      exact hr
    have hi : b ∈ I.ideal ⟨W, hW⟩ := by
      rw [← I.ker_subschemeι_app ⟨W, hW⟩]
      exact hz0
    rw [← hb, stalkIdeal_eq_map I _ ⟨W, hW⟩ hxW]
    exact Ideal.mem_map_of_mem _ hi

/-- At the integral generic point the defining ideal stalk is the ambient maximal ideal. -/
theorem generic_stalkIdeal [IsIntegral I.subscheme] :
    stalkIdeal I (I.subschemeι (genericPoint I.subscheme)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))) := by
  rw [stalkIdeal_eq_ker]
  let f := (I.subschemeι.stalkMap (genericPoint I.subscheme)).hom
  have he := IsLocalRing.maximalIdeal_comap f
  rw [IsLocalRing.maximalIdeal_eq_bot] at he
  exact he

variable [IsLocallyNoetherian X] (F : X.Modules) [F.IsFinitePresentation]

/-- The inclusion of the constructed annihilator is surjective at the generic point. -/
theorem generic_inclusion_surjective [IsIntegral I.subscheme]
    (hF : StalkAnnihilated F (I.subschemeι (genericPoint I.subscheme))) :
    Function.Surjective
      ((stalk (I.subschemeι (genericPoint I.subscheme))).map (inclusion I F)) := by
  intro m
  apply (stalk_range I F _ m).mpr
  intro r hr
  exact hF r (generic_stalkIdeal I ▸ hr) m

/-- The original generic stalk is recovered through the canonical inclusion. -/
def genericStalkEquiv [IsIntegral I.subscheme]
    (hF : StalkAnnihilated F (I.subschemeι (genericPoint I.subscheme))) :
    (sheaf I F).presheaf.stalk (I.subschemeι (genericPoint I.subscheme)) ≃ₗ[
      X.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))]
        F.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)) :=
  LinearEquiv.ofBijective (comparisonStalkLinear (inclusion I F) _)
    ⟨fun _ _ h ↦ (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (fun V ↦ ModuleSubobjectCoverEquality.app_injective (inclusion I F) V) _) h,
      generic_inclusion_surjective I F hF⟩

/-- Descend the constructed coherent annihilator to the actual closed subscheme. -/
def descent : I.subscheme.Modules := by
  have := sheaf_coherent I F
  exact GlobalClosedModuleDescent.descent I (sheaf I F) (idealKilled I F)

instance descent_coherent : (descent I F).IsFinitePresentation := by
  have := sheaf_coherent I F
  exact GlobalClosedModuleDescent.descent_isFinitePresentation I (sheaf I F) (idealKilled I F)

/-- The descended sheaf pushes forward to the canonical annihilator subsheaf. -/
def pushforwardIso : (pushforward I.subschemeι).obj (descent I F) ≅ sheaf I F := by
  have := sheaf_coherent I F
  exact GlobalClosedModuleDescent.pushforwardIso I (sheaf I F) (idealKilled I F)

/-- The actual ambient inclusion of the descended coherent sheaf. -/
def embedding : (pushforward I.subschemeι).obj (descent I F) ⟶ F :=
  (pushforwardIso I F).hom ≫ inclusion I F

instance embedding_mono : Mono (embedding I F) := by
  dsimp only [embedding]
  infer_instance

/-- The descended pushforward has the whole original stalk at the integral generic point. -/
def embeddingStalkEquiv [IsIntegral I.subscheme]
    (hF : StalkAnnihilated F (I.subschemeι (genericPoint I.subscheme))) :
    ((pushforward I.subschemeι).obj (descent I F)).presheaf.stalk
        (I.subschemeι (genericPoint I.subscheme)) ≃ₗ[
      X.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))]
        F.presheaf.stalk (I.subschemeι (genericPoint I.subscheme)) :=
  (comparisonStalkEquiv (pushforwardIso I F) _).trans (genericStalkEquiv I F hF)

/-- The generic identification is induced by the constructed embedding. -/
lemma embeddingStalkEquiv_apply [IsIntegral I.subscheme]
    (hF : StalkAnnihilated F (I.subschemeι (genericPoint I.subscheme)))
    (m : ((pushforward I.subschemeι).obj (descent I F)).presheaf.stalk
      (I.subschemeι (genericPoint I.subscheme))) :
    embeddingStalkEquiv I F hF m =
      (stalk (I.subschemeι (genericPoint I.subscheme))).map (embedding I F) m := by
  change _ = (stalk _).map ((pushforwardIso I F).hom ≫ inclusion I F) m
  rw [Functor.map_comp]
  rfl

end FLT.Mazur.CoherentClosedReduction
