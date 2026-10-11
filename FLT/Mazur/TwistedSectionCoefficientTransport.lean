/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionPushforwardNaturality
public import FLT.Mazur.TwistedSectionCartierTransport
public import FLT.Mazur.TwistedSectionLocalSplitting

/-!
# Coefficient isomorphisms retain split sections and full Cartier ideals

An actual coefficient isomorphism transports the section, its direct-image
map, and every equation of its zero ideal. These comparisons let affine
family criteria apply to the original restricted coefficient sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.TwistedSectionCoefficientTransport
open FCurve ModuleSheafTensor SplitLineAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) {L M : X.Modules} (e : L ≅ M)
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))

/-- The original section transported by the actual coefficient comparison. -/
def section_ : Γ(tensor M ((pullback f).obj B), ⊤) :=
  (congr e (Iso.refl _)).hom.app ⊤ s

/-- Coefficient transport preserves and detects splitting of the original direct-image map. -/
lemma locallySplit_iff :
    LocallySplit (twistedSectionPushforwardEquiv f M hB (section_ f e s)) ↔
      LocallySplit (twistedSectionPushforwardEquiv f L hB s) := by
  change LocallySplit (twistedSectionPushforwardEquiv f M hB
    ((map e.hom (𝟙 _)).app ⊤ s)) ↔ _
  rw [twistedSectionPushforwardEquiv_naturality]
  constructor
  · intro hs
    have ht := hs.postcompose _ ((pushforward f).mapIso e).symm
    simp only [Iso.symm_hom, Functor.mapIso_inv, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id] at ht
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using ht
  · intro hs
    exact hs.postcompose _ ((pushforward f).mapIso e)

/-- The transported tensor section has exactly the same full ideal. -/
lemma zeroIdeal (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) :
    lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s =
      lineSectionZeroIdeal (hM.tensor (hB.pullback f)) (section_ f e s) :=
  lineSectionZeroIdeal_eq_of_iso _ _ (congr e (Iso.refl _)) _ _ rfl

/-- Regularity and relative flatness are invariant under the coefficient comparison. -/
theorem relativeCartier_iff (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) :
    (Mono (globalSectionHom _ (section_ f e s)) ∧ RelativeEffectiveCartier f
      (lineSectionZeroIdeal (hM.tensor (hB.pullback f)) (section_ f e s))) ↔
    (Mono (globalSectionHom _ s) ∧ RelativeEffectiveCartier f
      (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s)) := by
  rw [zeroIdeal f e hB s hL hM]
  change (Mono (globalSectionHom _ ((congr e (Iso.refl _)).hom.app ⊤ s)) ∧ _) ↔ _
  rw [← globalSectionHom_naturality,
    mono_comp_iff_of_mono _ (congr e (Iso.refl _)).hom]

end FLT.Mazur.TwistedSectionCoefficientTransport
