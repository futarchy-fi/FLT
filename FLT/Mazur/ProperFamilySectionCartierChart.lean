/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilySplitDirectImageSections
public import FLT.Mazur.ProperLineRankOneChartDescent
public import FLT.Mazur.TwistedSectionCoefficientTransport

/-!
# Original split sections over subordinate affine family charts

The test open need not be affine or Noetherian. Restriction of the original
section has a relative Cartier full ideal whenever its image lies in an
acyclic affine chart of the original locally Noetherian family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperFamilySectionCartierChart
open FCurve LineSectionBaseChange ModuleSheafTensor
open TwistedSectionBaseChangeRegularity
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  TwistedSectionBaseChangeRegularity.section_
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (U : S.Opens) (hU : IsAffineOpen U)
  (hV : ∀ s : S, s ∈ U → ∀ n,
    Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))
  (W : T.Opens) (hW : W ≤ g ⁻¹ᵁ U)
  {B : T.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor ((pullback p).obj L) ((pullback q).obj B), ⊤))
  (hs : SplitLineAffineNeighborhood.LocallySplit
    (twistedSectionPushforwardEquiv q ((pullback p).obj L) hB s))

include h hU hV hW hs in
/-- Affine family geometry proves the Cartier property of the unmodified restricted section. -/
theorem regular_and_relativeCartier :
    Mono (globalSectionHom _ (pullGlobal (q ⁻¹ᵁ W).ι _ s)) ∧
      RelativeEffectiveCartier (q ∣_ W)
        (lineSectionZeroIdeal (((hL.pullback p).tensor (hB.pullback q)).pullback
          (q ⁻¹ᵁ W).ι) (pullGlobal (q ⁻¹ᵁ W).ι _ s)) := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  have hle : q ⁻¹ᵁ W ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hW
  let a := p.resLE (f ⁻¹ᵁ U) (q ⁻¹ᵁ W) hle
  let b := g.resLE U W hW
  have H : IsPullback a (q ∣_ W) (f ∣_ U) b := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE h hW (le_rfl : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U)
        (inf_eq_right.mpr hle).symm
  let N := (pullback (f ⁻¹ᵁ U).ι).obj L
  have hn := hL.pullback (f ⁻¹ᵁ U).ι
  have hv (t : U.toScheme) (n : ℕ) : Subsingleton
      (ModuleH ((pullback ((f ∣_ U).fiberι t)).obj N) (n + 1)) :=
    (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U).flip
      L hL t (n + 1)).mpr (hV (U.ι t) t.property n)
  let e : (pullback (q ⁻¹ᵁ W).ι).obj ((pullback p).obj L) ≅ (pullback a).obj N :=
    (pullbackComp (q ⁻¹ᵁ W).ι p).app L ≪≫
      (pullbackCongr (p.resLE_comp_ι hle).symm).app L ≪≫
        ((pullbackComp a (f ⁻¹ᵁ U).ι).app L).symm
  let t := section_ (q ⁻¹ᵁ W).ι (q ∣_ W) q W.ι
    (morphismRestrict_ι q W) ((pullback p).obj L) s
  have ht := (section_open_locallySplit_iff q ((pullback p).obj L) hB W s).mpr
    (hs.pullback _ W.ι)
  have ht' := (TwistedSectionCoefficientTransport.locallySplit_iff
    (q ∣_ W) e (hB.pullback W.ι) t).mpr ht
  have hc := (CartierAbel.familySection_locallySplit_iff H N hn
    (residueAlgebra_vanishing_of_geometric (f ∣_ U) N hn hv)
    ⟨(pullback W.ι).obj B, hB.pullback W.ι⟩ _).mp ht'
  have hc' := (TwistedSectionCoefficientTransport.relativeCartier_iff
    (q ∣_ W) e (hB.pullback W.ι) t ((hL.pullback p).pullback (q ⁻¹ᵁ W).ι)
      (hn.pullback a)).mp hc
  exact (TwistedSectionPullbackMonicity.relativeCartier_iff
    (q ⁻¹ᵁ W).ι (q ∣_ W) q W.ι (morphismRestrict_ι q W)
      ((pullback p).obj L) (hL.pullback p) hB s).mp hc'

end FLT.Mazur.ProperFamilySectionCartierChart
