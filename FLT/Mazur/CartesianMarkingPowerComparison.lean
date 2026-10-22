/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianMarkingLineComparison
public import FLT.Mazur.SectionPointPowerSectionComposition

/-!
# Canonical pole-power comparison between independent marked models

On the actual common Cartesian refinement, both model pole powers identify
with the power of the common marking. The resulting comparison preserves
the canonical powered section and is defined in every degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso

variable {W X Y T A B : Scheme}
  {v : W ⟶ T} {p : X ⟶ A} {q : Y ⟶ B}
  {c : W ⟶ X} {d : W ⟶ Y} {a : T ⟶ A} {b : T ⟶ B}
  [IsSeparated p] [IsSeparated q]
  (hc : IsPullback c v p a) (hd : IsPullback d v q b)
  (t : T ⟶ W) (s : A ⟶ X) (u : B ⟶ Y)
  (ht : t ≫ v = 𝟙 _) (hs : s ≫ p = 𝟙 _) (hu : u ≫ q = 𝟙 _)
  (hcs : t ≫ c = a ≫ s) (hdu : t ≫ d = b ≫ u)
  (hI : EffectiveCartier s.ker) (hJ : EffectiveCartier u.ker) (hK : EffectiveCartier t.ker)

/-- Compare the actual pole powers of two independent models on their common refinement. -/
def commonMarkingPowerIso (m : ℕ) :
    (pullback c).obj (tensorPower (divisorLineBundle s.ker hI) m) ≅
      (pullback d).obj (tensorPower (divisorLineBundle u.ker hJ) m) :=
  sectionPointPowerIso hc s t hs ht hcs hI hK m ≪≫
    (sectionPointPowerIso hd u t hu ht hdu hJ hK m).symm

/-- The comparison identifies the actual canonical powered sections from the two models. -/
theorem commonMarkingPowerIso_canonicalSection (m : ℕ) :
    (commonMarkingPowerIso hc hd t s u ht hs hu hcs hdu hI hJ hK m).hom.app ⊤
        (pullGlobal c _ (tensorPowerSection _ ⊤ (divisorSection hI ⊤) m)) =
      pullGlobal d _ (tensorPowerSection _ ⊤ (divisorSection hJ ⊤) m) := by
  change (sectionPointPowerIso hd u t hu ht hdu hJ hK m).inv.app ⊤
    ((sectionPointPowerIso hc s t hs ht hcs hI hK m).hom.app ⊤ _) = _
  rw [sectionPointPowerIso_canonicalSection hc t s ht hs hcs hI hK m]
  exact sectionIso_inv_of_eq (sectionPointPowerIso hd u t hu ht hdu hJ hK m) ⊤ _ _
    (sectionPointPowerIso_canonicalSection hd t u ht hu hdu hJ hK m)

/-- Reversing the order of the independent models inverts the actual power comparison. -/
theorem commonMarkingPowerIso_symm (m : ℕ) :
    (commonMarkingPowerIso hc hd t s u ht hs hu hcs hdu hI hJ hK m).symm =
      commonMarkingPowerIso hd hc t u s ht hu hs hdu hcs hJ hI hK m := by
  rfl

/-- Three independent model powers satisfy the actual cocycle equation on a common refinement. -/
theorem commonMarkingPowerIso_trans
    {Z C : Scheme} {r : Z ⟶ C} [IsSeparated r] {e : W ⟶ Z} {b' : T ⟶ C}
    (he : IsPullback e v r b') (z : C ⟶ Z) (hz : z ≫ r = 𝟙 _)
    (hez : t ≫ e = b' ≫ z) (hL : EffectiveCartier z.ker) (m : ℕ) :
    commonMarkingPowerIso hc hd t s u ht hs hu hcs hdu hI hJ hK m ≪≫
        commonMarkingPowerIso hd he t u z ht hu hz hdu hez hJ hL hK m =
      commonMarkingPowerIso hc he t s z ht hs hz hcs hez hI hL hK m := by
  simp only [commonMarkingPowerIso, Iso.trans_assoc, Iso.symm_self_id_assoc]

end FLT.Mazur.FCurve
