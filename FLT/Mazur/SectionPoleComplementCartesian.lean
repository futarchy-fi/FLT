/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleComplementBaseChange

/-!
# The actual Cartier complement square is cartesian

The retained marking complement is the inverse image of the original
complement. Its projection is therefore the actual base change, both
inside the total spaces and over the original base square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s)

/-- The actual complement projection forms the cartesian open square in the total spaces. -/
theorem sectionPointComplementMap_cartesian :
    IsPullback (sectionPointComplementMap h s t hs ht hst)
      (Scheme.Opens.ι (X := P) t.ker.support.compl)
      (Scheme.Opens.ι (X := X) s.ker.support.compl) p := by
  apply IsOpenImmersion.isPullback
  · exact (sectionPointComplementMap_ι h s t hs ht hst).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      (sectionPointComplement_preimage h s t hs ht hst).symm

/-- The retained complement is the actual arbitrary base change of the original complement. -/
theorem sectionPointComplementMap_baseCartesian :
    IsPullback (sectionPointComplementMap h s t hs ht hst)
      (Scheme.Opens.ι (X := P) t.ker.support.compl ≫ q)
      (Scheme.Opens.ι (X := X) s.ker.support.compl ≫ f) g :=
  (sectionPointComplementMap_cartesian h s t hs ht hst).paste_vert h

end FLT.Mazur.FCurve
