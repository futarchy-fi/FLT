/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomMarkedIsoPullback
public import FLT.Mazur.UniversalWeierstrassCyclicMarkedIsoPullback
public import FLT.Mazur.OddWeierstrassAuxiliaryAffineMarkedRigidity
public import FLT.Mazur.AffineBasePullbackDetection

/-!
# Uniqueness of genuine auxiliary-marked family comparisons on every source

Affine proper rigidity and detection by affine base tests prove uniqueness of
the actual group isomorphism, including on nonaffine and nonreduced sources.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels familyIso_conjugate_injective)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] auxiliarySchemeMarking cyclicHomSourceMarking
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (e d : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g))
  (he : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫ e.hom.hom.hom.hom =
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)
  (hd : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫ d.hom.hom.hom.hom =
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)

include he hd in
/-- Original auxiliary-marked group-family comparisons are unique on affine sources. -/
theorem cyclicHomAffineMarkedGroupIso_unique [IsAffine T] : e = d := by
  apply Iso.ext
  apply (CommGrp.forget (Over T)).map_injective
  exact congrArg Iso.hom (auxiliaryAffineMarkedIso_unique
    (cyclicHomAuxiliaryPoint n f) (cyclicHomAuxiliaryPoint n g)
    ((CommGrp.forget (Over T)).mapIso e) ((CommGrp.forget (Over T)).mapIso d)
    he hd)

include he hd in
/-- Original auxiliary-marked group-family comparisons are unique over every source scheme. -/
theorem cyclicHomMarkedGroupIso_unique : e = d := by
  apply Iso.ext
  apply (CommGrp.forget (Over T)).map_injective
  apply AffineBasePullbackDetection.hom_ext
  intro U _ k
  have h := cyclicHomAffineMarkedGroupIso_unique n (k ≫ f) (k ≫ g)
    (cyclicHomMarkedIsoPullback n f g e k) (cyclicHomMarkedIsoPullback n f g d k)
    (cyclicHomMarkedIsoPullback_auxiliary n f g e k he)
    (cyclicHomMarkedIsoPullback_auxiliary n f g d k hd)
  rw [cyclicHomMarkedIsoPullback_def, cyclicHomMarkedIsoPullback_def] at h
  have h' := familyIso_conjugate_injective (cyclicHomSourceGroupIso n f k)
    (cyclicHomSourceGroupIso n g k) _ _ h
  exact congrArg (fun z ↦ z.hom.hom.hom.hom) h'

/-- The original auxiliary-marked family has no nontrivial group automorphism on any source. -/
theorem cyclicHomMarkedGroupIso_eq_refl
    (e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f))
    (he : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      e.hom.hom.hom.hom =
      auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c) : e = Iso.refl _ :=
  cyclicHomMarkedGroupIso_unique n f f e (Iso.refl _) he (fun _ ↦ Category.comp_id _)

end FLT.Mazur.OddWeierstrassParameter
