/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleBaseChangeSections

/-!
# Normalized leading terms survive actual base change

Pull back the original leading frame through the cartesian comparison.
The resulting coordinate is the pullback of the original coefficient.
In particular, an originally normalized pole section stays normalized.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleLineBaseChangeIso
variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)

/-- The original leading frame transported to the actual changed divisor power. -/
def sectionPoleBaseChangeFrame (m : ℕ)
    (e : sectionPoleLine s hI m ≅ structureModule S) :
    sectionPoleLine t hJ m ≅ structureModule T :=
  (sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ m).symm ≪≫
    (pullback g).mapIso e ≪≫ modulePullbackUnitIso g

/-- Evaluation in the transported frame commutes with base change of leading sections. -/
theorem sectionPoleBaseChangeFrame_coordinate (m : ℕ)
    (e : sectionPoleLine s hI m ≅ structureModule S)
    (z : Γ(sectionPoleLine s hI m, ⊤)) :
    (sectionPoleBaseChangeFrame h s t hs ht hst hI hJ m e).hom.app ⊤
      ((sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ m).hom.app ⊤
        (pullGlobal g _ z)) = g.appTop (e.hom.app ⊤ z) := by
  have hi := congrArg (fun a ↦ a.app ⊤ (pullGlobal g _ z))
    (sectionPoleLineBaseChangeIso h s t hs ht hst hI hJ m).hom_inv_id
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app,
    ConcreteCategory.id_apply] at hi
  simp only [sectionPoleBaseChangeFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Hom.comp_app, ConcreteCategory.comp_apply, hi]
  rw [pullGlobal_naturality g e.hom]
  exact modulePullbackUnitIso_unit g ⊤ _

variable [IsSeparated q]

/-- The coefficient of a transported actual pole section is its original scalar pullback. -/
theorem sectionPoleBaseChangeFrame_leading (m : ℕ)
    (e : sectionPoleLine s hI (m + 1) ≅ structureModule S)
    (x : ModuleRingH f.appTop.hom
      (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    (sectionPoleBaseChangeFrame h s t hs ht hst hI hJ (m + 1) e).hom.app ⊤
      (sectionPoleLeading q t ht hJ m ((moduleH0Equiv _).symm
        (sectionPointPowerPullGlobal h s t hs ht hst hI hJ (m + 1)
          (moduleH0Equiv _ x)))) =
      g.appTop (e.hom.app ⊤ (sectionPoleLeading f s hs hI m x)) := by
  rw [sectionPoleLeading_baseChange]
  exact sectionPoleBaseChangeFrame_coordinate h s t hs ht hst hI hJ (m + 1) e _

/-- Normalization at one persists even for nonflat changes and nilpotent bases. -/
theorem sectionPoleBaseChangeFrame_normalized (m : ℕ)
    (e : sectionPoleLine s hI (m + 1) ≅ structureModule S)
    (x : ModuleRingH f.appTop.hom
      (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0)
    (hx : e.hom.app ⊤ (sectionPoleLeading f s hs hI m x) = (1 : Γ(S, ⊤))) :
    (sectionPoleBaseChangeFrame h s t hs ht hst hI hJ (m + 1) e).hom.app ⊤
      (sectionPoleLeading q t ht hJ m ((moduleH0Equiv _).symm
        (sectionPointPowerPullGlobal h s t hs ht hst hI hJ (m + 1)
          (moduleH0Equiv _ x)))) = (1 : Γ(T, ⊤)) := by
  rw [sectionPoleBaseChangeFrame_leading, hx, map_one]

end FLT.Mazur.FCurve
