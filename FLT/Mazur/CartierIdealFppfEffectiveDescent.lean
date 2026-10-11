/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealGluedMonicity
public import FLT.Mazur.LineImageCartier
public import FLT.Mazur.QuasicoherentImageIdealOrbits
public import FLT.Mazur.IdealSheafFlatDetection

/-!
# Effective fppf descent of full Cartier ideals

The full image of the descended embedding is Cartier and recovers the supplied
ideal under pullback. Equality is equality of ideal sheaves, including all
nonreduced structure. Faithful flatness gives uniqueness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemePicard
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y : Scheme.{0}} (p : Y ⟶ X)
  [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
  (h : I.comap (Limits.pullback.fst p p) = I.comap (Limits.pullback.snd p p))

local instance : (cartierIdealGluedLine p I hI h).val.IsQuasicoherent := by
  let _ := rankOne_finitePresentation _ (cartierIdealGluedLine p I hI h).property
  infer_instance

local instance : Mono (cartierIdealGluedInclusion p I hI h) :=
  cartierIdealGluedInclusion_mono p I hI h

/-- The full ideal obtained as the image of the descended actual embedding. -/
def cartierIdealDescended : X.IdealSheafData :=
  quasicoherentImageIdeal (cartierIdealGluedInclusion p I hI h)

/-- The constructed ideal is Cartier on the original base. -/
theorem cartierIdealDescended_cartier : EffectiveCartier (cartierIdealDescended p I hI h) :=
  image_effectiveCartier _ (cartierIdealGluedLine p I hI h).property

/-- The pulled-back glued line identifies with the module of the descended ideal comap. -/
def cartierIdealDescendedPullbackIso :
    (pullback p).obj (cartierIdealGluedLine p I hI h).val ≅
      idealModule ((cartierIdealDescended p I hI h).comap p) := by
  letI := idealModulePullbackHom_isIso_of_flat (cartierIdealDescended p I hI h)
    (cartierIdealDescended_cartier p I hI h) p
  exact (pullback p).mapIso (quasicoherentImageIdealIso (cartierIdealGluedInclusion p I hI h))
    ≪≫ asIso (idealModulePullbackHom (cartierIdealDescended p I hI h) p)

/-- The comparison retains the actual ideal inclusion after pullback. -/
lemma cartierIdealDescendedPullbackIso_inclusion :
    (cartierIdealDescendedPullbackIso p I hI h).hom ≫
        idealModuleι ((cartierIdealDescended p I hI h).comap p) =
      (pullback p).map (cartierIdealGluedInclusion p I hI h) ≫
        (modulePullbackUnitIso p).hom := by
  dsimp only [cartierIdealDescendedPullbackIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [Category.assoc, idealModulePullbackHom_ι]
  dsimp only [idealModulePullbackι]
  dsimp only [cartierIdealDescended]
  rw [← Functor.map_comp_assoc, quasicoherentImageIdealIso_comp]

/-- The entire descended ideal pulls back to the supplied ideal, with no radical taken. -/
theorem cartierIdealDescended_comap : (cartierIdealDescended p I hI h).comap p = I := by
  let _ := rankOne_finitePresentation _ (hI.idealModule_locallyFreeRankOne)
  let _ := rankOne_finitePresentation _
    (((cartierIdealDescended_cartier p I hI h).comap_of_flat p).idealModule_locallyFreeRankOne)
  let _ := rankOne_finitePresentation _ ((cartierIdealGluedLine p I hI h).property.pullback p)
  have h₁ := quasicoherentImageIdeal_eq_of_iso
    ((pullback p).map (cartierIdealGluedInclusion p I hI h) ≫ (modulePullbackUnitIso p).hom)
    (idealModuleι ((cartierIdealDescended p I hI h).comap p))
    (cartierIdealDescendedPullbackIso p I hI h)
    (cartierIdealDescendedPullbackIso_inclusion p I hI h)
  have h₂ := quasicoherentImageIdeal_eq_of_iso
    ((pullback p).map (cartierIdealGluedInclusion p I hI h) ≫ (modulePullbackUnitIso p).hom)
    (idealModuleι I) (cartierIdealGluedLineIso p I hI h)
    (cartierIdealGluedInclusion_recovery p I hI h).symm
  rw [quasicoherentImageIdeal_idealModuleι] at h₁ h₂
  exact h₁.symm.trans h₂

include hI h in
/-- Matching full Cartier ideals descend uniquely along an actual fppf morphism. -/
theorem existsUnique_cartierIdeal_descent :
    ∃! J : X.IdealSheafData, EffectiveCartier J ∧ J.comap p = I := by
  refine ⟨cartierIdealDescended p I hI h,
    ⟨cartierIdealDescended_cartier p I hI h, cartierIdealDescended_comap p I hI h⟩, ?_⟩
  intro J hJ
  exact idealSheaf_comap_injective p (hJ.2.trans (cartierIdealDescended_comap p I hI h).symm)

end FLT.Mazur.FCurve
