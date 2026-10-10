/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionCartierOpenDescent

/-!
# Restricting a relative Cartier section over a base open

The original zero ideal restricts by its full ideal-sheaf comap. Flatness over
the original base cancels the open immersion of the new base, so the section
is relative Cartier over that base open itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionCartierOpenDescent
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S) {M : X.Modules}
  (hM : LocallyFreeRankOne M) (s : Γ(M, ⊤)) [Mono (globalSectionHom M s)]

/-- Restriction of a full relative Cartier section is relative over every base open. -/
theorem relativeCartier_baseOpen
    (hC : RelativeEffectiveCartier f (lineSectionZeroIdeal hM s)) (U : S.Opens) :
    Mono (globalSectionHom _ (pullGlobal (f ⁻¹ᵁ U).ι M s)) ∧
      RelativeEffectiveCartier (f ∣_ U)
        (lineSectionZeroIdeal (hM.pullback (f ⁻¹ᵁ U).ι) (pullGlobal (f ⁻¹ᵁ U).ι M s)) := by
  have hp := hC.comap_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  rw [lineSectionZeroIdeal_pullGlobal (f ⁻¹ᵁ U).ι hM s hp.1]
  refine ⟨OpenSectionMonicity.pullGlobal_mono _ M s, hp.1, ?_⟩
  have ht : Flat
      (((lineSectionZeroIdeal hM s).comap (f ⁻¹ᵁ U).ι).subschemeι ≫ (f ∣_ U) ≫ U.ι) := by
    simpa only [morphismRestrict_ι] using hp.2
  exact MorphismProperty.of_postcomp @Flat _ U.ι
    (inferInstance : IsOpenImmersion U.ι) (by simpa only [Category.assoc] using ht)

end FLT.Mazur.SectionCartierOpenDescent
