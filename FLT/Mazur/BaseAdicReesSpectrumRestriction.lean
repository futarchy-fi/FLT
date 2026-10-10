/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleRefinement
public import FLT.Mazur.BaseAdicReesSpectrumComparison
public import FLT.Mazur.ModuleSheafIdentityRecovery

/-!
# Original restriction morphisms in fixed spectrum coordinates

The original coefficient restriction retains its composition law and overlap
comparison. Each original self-inclusion is the identity scheme map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.SheafPullbackPathComparison

/-- Evaluation of the path comparison agrees with the original objectwise comparison. -/
lemma app_compositeIso {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (N : C.Modules) :
    AffineIteratedPullbackSections.compositeIso a b c h N =
      (comparison a b c h).app N := rfl

end FLT.Mazur.SheafPullbackPathComparison

namespace FLT.Mazur.BaseAdicRees

open SheafPullbackPathComparison

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local semireducible] modelSpectrum
attribute [local irreducible] Scheme.Modules.pullback modelRestriction modelCompositeIso

/-- A chart's original self-inclusion is the identity scheme map. -/
lemma spectrumMap_self (U : X.affineOpens) :
    spectrumMap f J (U := U) le_rfl = 𝟙 (modelSpectrum f J U) := by
  apply (cancel_mono (spectrumSpaceMap f J U)).mp
  rw [spectrumMap_chart, Category.id_comp]

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- The original coefficient restriction, with its spectrum source and target fixed. -/
@[irreducible]
def spectrumRestriction {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (pullback (spectrumMap f J h)).obj (spectrumSheaf f J M V) ⟶
      spectrumSheaf f J M U :=
  modelRestriction f J M h

/-- Original restrictions remain invertible in the fixed spectrum presentation. -/
instance spectrumRestriction_isIso {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    IsIso (spectrumRestriction f J M h) := by
  unfold spectrumRestriction
  exact modelRestriction_isIso f J M h

/-- The fixed iterated comparison is the genuine pullback path comparison. -/
lemma spectrumCompositeIso_path {U V W : X.affineOpens}
    (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    spectrumCompositeIso f J M h k =
      (comparison (spectrumMap f J h) (spectrumMap f J k)
        (spectrumMap f J (h.trans k)) (spectrumMap_comp f J h k)).app
          (spectrumSheaf f J M W) := by
  exact (spectrumCompositeIso_eq f J M h k).trans (app_compositeIso _ _ _ _ _)

/-- Composition of original coefficient restrictions retains the geometric comparison. -/
lemma spectrumRestriction_comp {U V W : X.affineOpens}
    (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) :
    (pullback (spectrumMap f J h)).map (spectrumRestriction f J M k) ≫
        spectrumRestriction f J M h =
      (spectrumCompositeIso f J M h k).hom ≫ spectrumRestriction f J M (h.trans k) := by
  unfold spectrumRestriction spectrumCompositeIso
  exact modelRestriction_comp_forward f J M h k

/-- The affine overlap map retains both original coefficient restrictions. -/
lemma spectrumAffineOverlap_restriction {U V W : X.affineOpens}
    (h : W.1 ≤ U.1) (k : W.1 ≤ V.1) :
    (spectrumAffineOverlap f J M h k).hom ≫ spectrumRestriction f J M k =
      spectrumRestriction f J M h := by
  unfold spectrumAffineOverlap spectrumRestriction
  exact modelAffineOverlap_hom_comp f J M h k

end FLT.Mazur.BaseAdicRees
