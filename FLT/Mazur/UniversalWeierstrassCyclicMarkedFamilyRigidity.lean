/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicMarkedIsoPullback
public import FLT.Mazur.UniversalWeierstrassAuxiliaryAffineMarkedRigidity
public import FLT.Mazur.AffineBasePullbackDetection

/-!
# Uniqueness of genuine full marked family comparisons on every source

Affine proper rigidity and detection by affine base tests prove uniqueness of
the actual group isomorphism, including on nonaffine and nonreduced sources.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] auxiliarySchemeGroup cyclicSchemeOriginalMarking
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
  (e d : auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n g))
  (he : ∀ c : CyclicLabels n, cyclicSchemeOriginalMarking n f c ≫ e.hom.hom.hom.hom =
    cyclicSchemeOriginalMarking n g c)
  (hd : ∀ c : CyclicLabels n, cyclicSchemeOriginalMarking n f c ≫ d.hom.hom.hom.hom =
    cyclicSchemeOriginalMarking n g c)

include he hd in
/-- Original full marked group-family comparisons are unique on affine sources. -/
theorem cyclicAffineMarkedGroupIso_unique [IsAffine T] : e = d := by
  apply Iso.ext
  apply (CommGrp.forget (Over T)).map_injective
  exact congrArg Iso.hom (auxiliaryAffineMarkedIso_unique
    (cyclicSchemeAuxiliaryPoint n f) (cyclicSchemeAuxiliaryPoint n g)
    ((CommGrp.forget (Over T)).mapIso e) ((CommGrp.forget (Over T)).mapIso d)
    (cyclicFamilyIso_auxiliary_marking n f g _ he)
    (cyclicFamilyIso_auxiliary_marking n f g _ hd))

include he hd in
/-- Original full marked group-family comparisons are unique over every source scheme. -/
theorem cyclicMarkedGroupIso_unique : e = d := by
  apply Iso.ext
  apply (CommGrp.forget (Over T)).map_injective
  apply AffineBasePullbackDetection.hom_ext
  intro U _ k
  have h := cyclicAffineMarkedGroupIso_unique n (k ≫ f) (k ≫ g)
    (cyclicMarkedFamilyIsoPullback n f g e k) (cyclicMarkedFamilyIsoPullback n f g d k)
    (cyclicMarkedFamilyIsoPullback_marking n f g e k he)
    (cyclicMarkedFamilyIsoPullback_marking n f g d k hd)
  rw [cyclicMarkedFamilyIsoPullback_def, cyclicMarkedFamilyIsoPullback_def] at h
  have h' := familyIso_conjugate_injective (cyclicSourceOriginalGroupIso n f k)
    (cyclicSourceOriginalGroupIso n g k) _ _ h
  exact congrArg (fun z ↦ z.hom.hom.hom.hom) h'

/-- The original full marked family has no nontrivial group automorphism on any source. -/
theorem cyclicMarkedGroupIso_eq_refl
    (e : auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f))
    (he : ∀ c : CyclicLabels n, cyclicSchemeOriginalMarking n f c ≫ e.hom.hom.hom.hom =
      cyclicSchemeOriginalMarking n f c) : e = Iso.refl _ :=
  cyclicMarkedGroupIso_unique n f f e (Iso.refl _) he (fun _ ↦ Category.comp_id _)

end FLT.Mazur.UniversalWeierstrass
