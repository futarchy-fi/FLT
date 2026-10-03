/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.IdealModulePullbackRestrict
public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# Positive divisor pullback from the canonical ideal comparison

When the actual ideal pullback comparison is invertible, duality identifies
the positive divisor sheaves and preserves evaluation and the canonical
section. Open immersions supply the ideal-isomorphism instance automatically.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} {I : Y.IdealSheafData} {J : X.IdealSheafData}

/-- An invertible canonical ideal comparison induces the positive divisor isomorphism. -/
def divisorLinePullbackIsoOfEq (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ :=
  moduleSheafDualPullbackIso f hI.idealModule_locallyFreeRankOne ≪≫
    (moduleSheafDualIso _ (idealModulePullbackIsoOfEq I f J h)).symm

/-- The forward map is the canonical dual comparison through the actual ideal isomorphism. -/
lemma divisorLinePullbackIsoOfEq_hom (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (divisorLinePullbackIsoOfEq f hI hJ h).hom =
      moduleSheafDualPullbackViaIso f (idealModule I) (idealModulePullbackIsoOfEq I f J h) := rfl

/-- The positive isomorphism preserves the canonical section map. -/
@[reassoc]
lemma divisorLinePullbackIsoOfEq_section (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (pullback f).map (divisorSectionMap hI) ≫ (divisorLinePullbackIsoOfEq f hI hJ h).hom =
      (modulePullbackUnitIso f).hom ≫ divisorSectionMap hJ :=
  moduleSheafDualPullbackViaIso_section f (idealModulePullbackIsoOfEq I f J h)
    (idealModuleι I) (idealModuleι J) (idealModulePullbackIsoOfEq_ι I f J h)

/-- The positive isomorphism preserves evaluation against the corresponding ideal section. -/
lemma divisorLinePullbackIsoOfEq_eval (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] (U : X.Opens)
    (φ : Γ((pullback f).obj (moduleSheafDual (idealModule I)), U))
    (s : Γ((pullback f).obj (idealModule I), U)) :
    moduleDualEval (idealModule J) U ((divisorLinePullbackIsoOfEq f hI hJ h).hom.app U φ)
      ((idealModulePullbackIsoOfEq I f J h).hom.app U s) =
      (moduleDualPullbackPairing f (idealModule I)).app U (ModuleSheafTensor.pure _ _ U φ s) :=
  moduleSheafDualPullbackViaIso_eval f (idealModule I) (idealModulePullbackIsoOfEq I f J h)
    U φ s
/-- The pulled-back canonical section maps to the target canonical section. -/
lemma divisorLinePullbackIsoOfEq_section_apply (f : X ⟶ Y) (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] (U : X.Opens) :
    (divisorLinePullbackIsoOfEq f hI hJ h).hom.app U
      (((pullback f).map (divisorSectionMap hI)).app U
        ((modulePullbackUnitIso f).inv.app U (1 : Γ(X, U)))) = divisorSection hJ U := by
  have hs := congrArg (fun k ↦ k.app U ((modulePullbackUnitIso f).inv.app U (1 : Γ(X, U))))
    (divisorLinePullbackIsoOfEq_section f hI hJ h)
  have hu := congrArg (fun k ↦ k.app U (1 : Γ(X, U))) (modulePullbackUnitIso f).inv_hom_id
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
    ConcreteCategory.id_apply] at hs hu
  rw [hu] at hs
  exact hs
end FLT.Mazur.FCurve
