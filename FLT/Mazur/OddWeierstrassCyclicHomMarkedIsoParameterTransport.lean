/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomMarkedGroupRigidity

/-!
# Equality transport of specified independently marked comparisons

Transport changes only the expressions for the original parameters. It retains
the specified group isomorphism and both independent markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g f' g' : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : f' = f) (hg : g' = g)
  (e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g))

/-- Retain the specified comparison under equality of its original parameters. -/
irreducible_def cyclicHomMarkedIsoTransport :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f') ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g') := by
  subst f'
  subst g'
  exact e

/-- Parameter transport retains every auxiliary marking equation. -/
theorem cyclicHomMarkedIsoTransport_auxiliary
    (ha : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c)
    (c : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f') c ≫
      (cyclicHomMarkedIsoTransport n f g f' g' hf hg e).hom.hom.hom.hom =
        auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g') c := by
  subst f'
  subst g'
  rw [cyclicHomMarkedIsoTransport_def]
  exact ha c

/-- Parameter transport retains every cyclic equation, including coincident sections. -/
theorem cyclicHomMarkedIsoTransport_cyclic
    (hc : ∀ c : Multiplicative (ZMod n), cyclicHomSourceMarking n f c ≫
      e.hom.hom.hom.hom = cyclicHomSourceMarking n g c) (c : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n f' c ≫
      (cyclicHomMarkedIsoTransport n f g f' g' hf hg e).hom.hom.hom.hom =
        cyclicHomSourceMarking n g' c := by
  subst f'
  subst g'
  rw [cyclicHomMarkedIsoTransport_def]
  exact hc c

end FLT.Mazur.OddWeierstrassParameter
