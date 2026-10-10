/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSectionSplittingCriterion
public import FLT.Mazur.TwistedSectionCartierTransport
public import FLT.Mazur.SectionCartierBaseOpen

/-!
# Cartier sections from splitting on an affine cover of the base

Apply the proper affine criterion to the transported original section on
each base chart. The tensor comparison preserves its full zero ideal, and
the inverse-image open cover descends regularity and flatness to the original
section on the entire family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperSectionAffineCoverCartier
open FCurve ModuleSheafTensor SplitLineAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  TwistedSectionBaseChangeRegularity.section_
variable {X S : Scheme.{0}} {ι : Type*} (f : X ⟶ S)
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))
  (U : ι → S.Opens) [∀ i, IsAffine (U i).toScheme]
  [∀ i, IsNoetherianRing Γ((U i).toScheme, ⊤)]
  (hV : ∀ i (z : PrimeSpectrum Γ((U i).toScheme, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine
      (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L) z) (n + 1)))

include hV in
/-- Splitting of the actual transported maps on a base cover gives a global Cartier divisor. -/
theorem regular_and_relativeCartier (hU : iSup U = ⊤)
    (hs : ∀ i, LocallySplit
      (twistedSectionPushforwardEquiv (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L)
        (hB.pullback (U i).ι)
        (TwistedSectionBaseChangeRegularity.section_ (f ⁻¹ᵁ U i).ι (f ∣_ U i)
          f (U i).ι (morphismRestrict_ι f (U i)) L s))) :
    Mono (globalSectionHom _ s) ∧
      RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  apply SectionCartierOpenDescent.relativeCartier_of_cover f
    (hL.tensor (hB.pullback f)) s (fun i ↦ f ⁻¹ᵁ U i) (f.iSup_preimage_eq_top hU)
  intro i
  have hp := ProperSplitSectionRelativeCartier.regular_and_relativeCartier
    (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L) (hL.pullback (f ⁻¹ᵁ U i).ι)
    (hV i) (hB.pullback (U i).ι) _ (hs i)
  have hc := (TwistedSectionPullbackMonicity.relativeCartier_iff
    (f ⁻¹ᵁ U i).ι (f ∣_ U i) f (U i).ι (morphismRestrict_ι f (U i)) L hL hB s).mp hp
  refine ⟨hc.1, hc.2.1, ?_⟩
  have := hc.2.2
  rw [← morphismRestrict_ι f (U i), ← Category.assoc]
  infer_instance

include hV in
/-- Chartwise splitting detects the full global relative Cartier condition. -/
theorem locallySplit_iff (hU : iSup U = ⊤) :
    (∀ i, LocallySplit
      (twistedSectionPushforwardEquiv (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L)
        (hB.pullback (U i).ι)
        (TwistedSectionBaseChangeRegularity.section_ (f ⁻¹ᵁ U i).ι (f ∣_ U i)
          f (U i).ι (morphismRestrict_ι f (U i)) L s))) ↔
    Mono (globalSectionHom _ s) ∧
      RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  constructor
  · exact regular_and_relativeCartier f L hL hB s U hV hU
  · rintro ⟨hm, hC⟩ i
    have hc := SectionCartierOpenDescent.relativeCartier_baseOpen f
      (hL.tensor (hB.pullback f)) s hC (U i)
    apply (ProperSectionSplittingCriterion.locallySplit_iff (f ∣_ U i)
      ((pullback (f ⁻¹ᵁ U i).ι).obj L) (hL.pullback (f ⁻¹ᵁ U i).ι)
      (hV i) (hB.pullback (U i).ι) _).mpr
    exact (TwistedSectionPullbackMonicity.relativeCartier_iff
      (f ⁻¹ᵁ U i).ι (f ∣_ U i) f (U i).ι (morphismRestrict_ι f (U i)) L hL hB s).mpr hc

end FLT.Mazur.ProperSectionAffineCoverCartier
