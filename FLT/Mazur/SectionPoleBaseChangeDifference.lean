/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleBaseChangeNormalization
public import FLT.Mazur.ModuleFrameComparisonUnit

/-!
# Independent normalized sections after actual base change

An independently chosen section normalized in the transported leading frame
differs from the original transported section by a unique lower-pole section.
No compatibility of chosen splittings is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleBaseChangeFrame
variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] [IsSeparated q] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier t.ker)
  (m : ℕ) (e : sectionPoleLine s hI (m + 1) ≅ structureModule S)
  (x : ModuleRingH f.appTop.hom
    (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0)
  (y : ModuleRingH q.appTop.hom
    (tensorPower (divisorLineBundle t.ker hJ) (m + 1)) 0)

/-- Actual base change of a positive pole class with its changed-base scalar module. -/
def sectionPolePullH0 : ModuleRingH q.appTop.hom
    (tensorPower (divisorLineBundle t.ker hJ) (m + 1)) 0 :=
  (moduleH0Equiv _).symm
    (sectionPointPowerPullGlobal h s t hs ht hst hI hJ (m + 1) (moduleH0Equiv _ x))

/-- Independent normalization leaves a unique correction in the original lower pole module. -/
theorem sectionPoleBaseChangeDifference_existsUnique
    (hx : e.hom.app ⊤ (sectionPoleLeading f s hs hI m x) = (1 : Γ(S, ⊤)))
    (hy : (sectionPoleBaseChangeFrame h s t hs ht hst hI hJ (m + 1) e).hom.app ⊤
      (sectionPoleLeading q t ht hJ m y) = (1 : Γ(T, ⊤))) :
    ∃! z : ModuleRingH q.appTop.hom (tensorPower (divisorLineBundle t.ker hJ) m) 0,
      y = sectionPolePullH0 h s t hs ht hst hI hJ m x +
        divisorPowerRingStep q.appTop.hom hJ m z := by
  let v : ModuleRingH q.appTop.hom
      (tensorPower (divisorLineBundle t.ker hJ) (m + 1)) 0 :=
    (moduleH0Equiv _).symm
      (sectionPointPowerPullGlobal h s t hs ht hst hI hJ (m + 1) (moduleH0Equiv _ x))
  have hv := sectionPoleBaseChangeFrame_normalized h s t hs ht hst hI hJ m e x hx
  have he : sectionPoleLeading q t ht hJ m y = sectionPoleLeading q t ht hJ m v := by
    apply (ConcreteCategory.bijective_of_isIso
      ((sectionPoleBaseChangeFrame h s t hs ht hst hI hJ (m + 1) e).hom.app ⊤)).injective
    exact hy.trans hv.symm
  have hz : sectionPoleLeading q t ht hJ m (y - v) = 0 := by
    rw [map_sub, he, sub_self]
  obtain ⟨z, hz⟩ := (sectionPoleLeading_eq_zero_iff q t ht hJ m _).mp hz
  refine ⟨z, ?_, ?_⟩
  · change y = v + divisorPowerRingStep q.appTop.hom hJ m z
    rw [hz]
    abel
  · intro z' hz'
    apply divisorPowerRingStep_injective q.appTop.hom hJ m
    rw [hz, eq_sub_iff_add_eq]
    exact (add_comm _ _).trans hz'.symm

/-- A new independent leading frame contributes its actual unit and a unique lower correction. -/
theorem sectionPoleBaseChangeFrameDifference_existsUnique
    (v : sectionPoleLine t hJ (m + 1) ≅ structureModule T)
    (hx : e.hom.app ⊤ (sectionPoleLeading f s hs hI m x) = (1 : Γ(S, ⊤)))
    (hy : v.hom.app ⊤ (sectionPoleLeading q t ht hJ m y) = (1 : Γ(T, ⊤))) :
    ∃! z : ModuleRingH q.appTop.hom (tensorPower (divisorLineBundle t.ker hJ) m) 0,
      y = (frameComparisonUnit
        (sectionPoleBaseChangeFrame h s t hs ht hst hI hJ (m + 1) e) v ⊤ : Γ(T, ⊤)) •
        sectionPolePullH0 h s t hs ht hst hI hJ m x + divisorPowerRingStep q.appTop.hom hJ m z := by
  let a := sectionPoleBaseChangeFrame h s t hs ht hst hI hJ (m + 1) e
  let c : Γ(T, ⊤) := (frameComparisonUnit a v ⊤ : Γ(T, ⊤))
  let x' : ModuleRingH q.appTop.hom
      (tensorPower (divisorLineBundle t.ker hJ) (m + 1)) 0 :=
    (moduleH0Equiv _).symm
      (sectionPointPowerPullGlobal h s t hs ht hst hI hJ (m + 1) (moduleH0Equiv _ x))
  have hx' : a.hom.app ⊤ (sectionPoleLeading q t ht hJ m x') = (1 : Γ(T, ⊤)) :=
    sectionPoleBaseChangeFrame_normalized h s t hs ht hst hI hJ m e x hx
  have hy' : a.hom.app ⊤ (sectionPoleLeading q t ht hJ m y) = c :=
    frameComparisonUnit_of_coefficient_one a v ⊤ _ hy
  have hz : sectionPoleLeading q t ht hJ m (y - c • x') = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (a.hom.app ⊤)).injective
    rw [_root_.map_sub, _root_.map_smul, _root_.map_sub, Hom.app_smul, hy', hx', map_zero,
      smul_eq_mul, mul_one, sub_self]
  obtain ⟨z, hz⟩ := (sectionPoleLeading_eq_zero_iff q t ht hJ m _).mp hz
  refine ⟨z, ?_, ?_⟩
  · change y = c • x' + divisorPowerRingStep q.appTop.hom hJ m z
    rw [hz]
    abel
  · intro z' hz'
    apply divisorPowerRingStep_injective q.appTop.hom hJ m
    rw [hz, eq_sub_iff_add_eq]
    exact (add_comm _ _).trans hz'.symm

end FLT.Mazur.FCurve
