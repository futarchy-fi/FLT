/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRelabelSections

/-!
# Common relabeling retains independent original frames and prescribed powers

Any original subgroup comparison preserving a specified frame and generator
extends along the common finite action. The new comparison keeps the original
frame with its prescribed permutation and all original generator powers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) (g : T ⟶ S) (b : Bool) (q : T ⟶ normalizedLocus n b)
  (a : CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g))
  (m : Labels (normalizedAuxiliaryOrder b) →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (hm : ∀ i, pullSection q (normalizedAuxiliaryMarking n b i) ≫ a.curve.hom.group = m i)
  {P : 𝟙_ (Over S) ⟶ H.carrier}
  (hP : pullSection q (normalizedGenerator n b) ≫ a.subgroup.hom = pullSection g P)

include hm hP in
/-- Relabeling the actual atlas retains the original frame and all prescribed generator powers. -/
theorem relabeled_prescribed_sections (e : RelabelGroup n) :
    ∃ aR : CompatibleIso
      ((normalizedSubgroup n b).baseChange (q ≫ (normalizedRelabelAction n b e).hom))
      (H.baseChange g),
      (∀ i, pullSection (q ≫ (normalizedRelabelAction n b e).hom)
        (normalizedAuxiliaryMarking n b i) ≫ aR.curve.hom.group =
          m ((normalizedAuxiliaryRelabel n e b).symm i)) ∧
      ∀ r : ℕ, (pullSection (q ≫ (normalizedRelabelAction n b e).hom)
        (normalizedGenerator n b) ^ r) ≫ aR.subgroup.hom =
          pullSection g (P ^ (e.2.2.symm (.ofAdd (r : ZMod n))).toAdd.val) := by
  obtain ⟨c, hc, hcP⟩ := normalizedRelabel_sections n b q e
  refine ⟨c.trans a, ?_, ?_⟩
  · intro i
    exact CompatibleIso.group_section_trans c a _ _ _ (hc i)
      (hm ((normalizedAuxiliaryRelabel n e b).symm i))
  · intro r
    change _ ≫ (c.subgroup.hom ≫ a.subgroup.hom) = _
    rw [← Category.assoc, hcP, pow_comp, hP, section_pow]

end FLT.Mazur.CyclicCharacteristicAtlas
