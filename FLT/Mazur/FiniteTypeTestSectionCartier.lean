/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestAcyclicDirectImage
public import FLT.Mazur.ProperFamilySectionCartierDescent

/-!
# Full Cartier ideals of independent sections on unrestricted tests

Affine approximation applies to the independently chosen coefficient line.
Transport back preserves its original section and full zero ideal. Open descent
then constructs regularity and relative flatness on the original test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  (L : X.Modules) (hL : LocallyFreeRankOne L) (hA : GeometricAcyclicRankOne f L)
  {B : S.Modules} (hB : LocallyFreeRankOne B) (s : Γ(tensor L ((pullback f).obj B), ⊤))
  (hs : SplitLineAffineNeighborhood.LocallySplit (twistedSectionPushforwardEquiv f L hB s))

include h hA hs in
/-- Every split original section has a full relative Cartier ideal on any affine test. -/
theorem finiteTypeAffine_section_relativeCartier [IsAffine S] :
    Mono (globalSectionHom _ s) ∧
      RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  obtain ⟨Z, T, r, p, b, M, hT, hr, hflat, hint, hM, H, ⟨e⟩⟩ :=
    Approximation.finiteTypeAffine_independent_line_model h L hL
  let t := TwistedSectionCoefficientTransport.section_ f e.symm s
  have ht := (TwistedSectionCoefficientTransport.locallySplit_iff f e.symm hB s).mpr hs
  have hA' := (geometricAcyclicRankOne_iso f e).mpr hA
  have hc := ProperFamilySectionCartierDescent.regular_and_relativeCartier H M hM hB t ht
    (fun x n ↦ (hA' x).1 n)
  exact (TwistedSectionCoefficientTransport.relativeCartier_iff f e.symm hB s
    hL (hM.pullback p)).mp hc

include h hA hs in
/-- The unmodified section has a regular full relative Cartier ideal on every test scheme. -/
theorem finiteTypeTest_section_relativeCartier :
    Mono (globalSectionHom _ s) ∧
      RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  let _ (U : S.affineOpens) : IsAffine U.1.toScheme := U.2
  apply SectionCartierOpenDescent.relativeCartier_of_cover f (hL.tensor (hB.pullback f)) s
    (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1) (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  intro U
  let t := TwistedSectionBaseChangeRegularity.section_ (f ⁻¹ᵁ U.1).ι (f ∣_ U.1)
    f U.1.ι (morphismRestrict_ι f U.1) L s
  have ht := (TwistedSectionBaseChangeRegularity.section_open_locallySplit_iff f L hB U.1 s).mpr
    (hs.pullback _ U.1.ι)
  have ha := geometricAcyclicRankOne_baseChange f
    (isPullback_morphismRestrict f U.1).flip L hL hA
  have hc := finiteTypeAffine_section_relativeCartier
    ((isPullback_morphismRestrict f U.1).flip.paste_horiz h)
    ((pullback (f ⁻¹ᵁ U.1).ι).obj L) (hL.pullback _) ha (hB.pullback U.1.ι) t ht
  have hd := (TwistedSectionPullbackMonicity.relativeCartier_iff
    (f ⁻¹ᵁ U.1).ι (f ∣_ U.1) f U.1.ι (morphismRestrict_ι f U.1) L hL hB s).mp hc
  refine ⟨hd.1, hd.2.1, ?_⟩
  have := hd.2.2
  rw [← morphismRestrict_ι f U.1, ← Category.assoc]
  infer_instance

end FLT.Mazur.CartierAbel
