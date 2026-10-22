/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPointLineCoherence
public import FLT.Mazur.DivisorLinePullbackComposition

/-!
# Composition of canonical marked line and pole-power recoveries

Successive Cartesian refinements give the same canonical marked line
comparison as their composite. The actual pullback compositor is retained,
and the equality propagates to every pole power.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso

variable {X Y Z A B C : Scheme}
  {p : X ⟶ A} {q : Y ⟶ B} {r : Z ⟶ C}
  {f : X ⟶ Y} {g : Y ⟶ Z} {a : A ⟶ B} {b : B ⟶ C}
  [IsSeparated q] [IsSeparated r]
  (hf : IsPullback f p q a) (hg : IsPullback g q r b)
  (s : A ⟶ X) (t : B ⟶ Y) (u : C ⟶ Z)
  (hs : s ≫ p = 𝟙 _) (ht : t ≫ q = 𝟙 _) (hu : u ≫ r = 𝟙 _)
  (hst : s ≫ f = a ≫ t) (htu : t ≫ g = b ≫ u)
  (hsu : s ≫ (f ≫ g) = (a ≫ b) ≫ u)
  (hI : EffectiveCartier u.ker) (hJ : EffectiveCartier t.ker) (hK : EffectiveCartier s.ker)

/-- Canonical marked-line recovery agrees with the composite of Cartesian refinements. -/
theorem sectionPointLineIso_comp :
    (pullbackComp f g).symm.app (divisorLineBundle u.ker hI) ≪≫
        (pullback f).mapIso (sectionPointLineIso hg u t hu ht htu hI hJ) ≪≫
          sectionPointLineIso hf t s ht hs hst hJ hK =
      sectionPointLineIso (hf.paste_horiz hg) u s hu hs hsu hI hK := by
  exact ((sectionPointLineIso_compatible hg u t hu ht htu hI hJ).comp
    (sectionPointLineIso_compatible hf t s ht hs hst hJ hK)).ext
      (sectionPointLineIso_compatible (hf.paste_horiz hg) u s hu hs hsu hI hK)

/-- Every pole power agrees under successive and composite Cartesian recovery. -/
theorem sectionPointPowerIso_comp (m : ℕ) :
    (pullbackComp f g).symm.app (tensorPower (divisorLineBundle u.ker hI) m) ≪≫
        (pullback f).mapIso (sectionPointPowerIso hg u t hu ht htu hI hJ m) ≪≫
          sectionPointPowerIso hf t s ht hs hst hJ hK m =
      sectionPointPowerIso (hf.paste_horiz hg) u s hu hs hsu hI hK m := by
  have he := sectionPointLineIso_comp hf hg s t u hs ht hu hst htu hsu hI hJ hK
  simpa only [sectionPointPowerIso_eq, he] using
    tensorPowerPullbackComparison_comp f g (sectionPointLineIso hg u t hu ht htu hI hJ)
      (sectionPointLineIso hf t s ht hs hst hJ hK) m

end FLT.Mazur.FCurve
