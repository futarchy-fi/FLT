/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPointLineComposition
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Actual pole sections under successive Cartesian refinements

The canonical sections of all pole powers are preserved. Transport of any
original pole section, including a chosen coordinate section, agrees under
successive refinement and direct recovery along the composite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso

/-- The actual canonical pole section is retained in every degree, including zero. -/
theorem sectionPointPowerIso_canonicalSection
    {X Y A B : Scheme} {p : X ⟶ A} {q : Y ⟶ B} {f : X ⟶ Y} {a : A ⟶ B}
    [IsSeparated q] (hf : IsPullback f p q a)
    (s : A ⟶ X) (t : B ⟶ Y) (hs : s ≫ p = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hst : s ≫ f = a ≫ t) (hI : EffectiveCartier t.ker) (hJ : EffectiveCartier s.ker)
    (m : ℕ) :
    (sectionPointPowerIso hf t s ht hs hst hI hJ m).hom.app ⊤
        (pullGlobal f _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) m)) =
      tensorPowerSection _ ⊤ (divisorSection hJ ⊤) m :=
  (sectionPointLineIso_compatible hf t s ht hs hst hI hJ).tensorPower_section m

/-- Actual pole coordinates do not change when recovery is factored through a model refinement. -/
theorem sectionPointPowerIso_comp_sections
    {X Y Z A B C : Scheme} {p : X ⟶ A} {q : Y ⟶ B} {r : Z ⟶ C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {a : A ⟶ B} {b : B ⟶ C}
    [IsSeparated q] [IsSeparated r]
    (hf : IsPullback f p q a) (hg : IsPullback g q r b)
    (s : A ⟶ X) (t : B ⟶ Y) (u : C ⟶ Z)
    (hs : s ≫ p = 𝟙 _) (ht : t ≫ q = 𝟙 _) (hu : u ≫ r = 𝟙 _)
    (hst : s ≫ f = a ≫ t) (htu : t ≫ g = b ≫ u)
    (hsu : s ≫ (f ≫ g) = (a ≫ b) ≫ u)
    (hI : EffectiveCartier u.ker) (hJ : EffectiveCartier t.ker) (hK : EffectiveCartier s.ker)
    (m : ℕ) (x : Γ(tensorPower (divisorLineBundle u.ker hI) m, ⊤)) :
    (sectionPointPowerIso hf t s ht hs hst hJ hK m).hom.app ⊤
        (pullGlobal f _ ((sectionPointPowerIso hg u t hu ht htu hI hJ m).hom.app ⊤
          (pullGlobal g _ x))) =
      (sectionPointPowerIso (hf.paste_horiz hg) u s hu hs hsu hI hK m).hom.app ⊤
        (pullGlobal (f ≫ g) _ x) := by
  have he := congrArg (fun e ↦ e.hom.app ⊤ (pullGlobal (f ≫ g) _ x))
    (sectionPointPowerIso_comp hf hg s t u hs ht hu hst htu hsu hI hJ hK m)
  change (sectionPointPowerIso hf t s ht hs hst hJ hK m).hom.app ⊤
    (((pullback f).map (sectionPointPowerIso hg u t hu ht htu hI hJ m).hom).app ⊤
      (((pullbackComp f g).inv.app _).app ⊤ (pullGlobal (f ≫ g) _ x))) = _ at he
  rw [pullGlobal_comp, pullGlobal_naturality] at he
  exact he

end FLT.Mazur.FCurve
