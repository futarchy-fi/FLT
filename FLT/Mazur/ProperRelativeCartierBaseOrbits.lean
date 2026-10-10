/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRelativeCartierAtlasQuotient
public import FLT.Mazur.TwistedSectionBaseLineNaturality
public import FLT.Mazur.LineSheafDualInvolution
public import FLT.Mazur.CartierAbelRelativeQuotient

/-!
# Retained base-line orbits preserve original relative Cartier divisors

The dual-source relation is equivalent to an actual base-line isomorphism
carrying the original tensor section to the other. Its pulled tensor
isomorphism therefore gives the existing total-space section relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [Surjective f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- Retained orbits use original base-line isomorphisms and the actual original sections. -/
theorem relativeBaseLineSetoid_iff_iso (s t : RelativeSection f L hL) :
    (relativeBaseLineSetoid f L hL hV).r s t ↔
      ∃ e : s.val.baseLine.val ≅ t.val.baseLine.val,
        (map (𝟙 L) ((pullback f).map e.hom)).app ⊤ s.val.section_ = t.val.section_ := by
  rw [relativeBaseLineSetoid_iff]
  constructor
  · rintro ⟨a, ha⟩
    let e := lineIsoOfDualIso s.val.baseLine.property t.val.baseLine.property a.symm
    refine ⟨e, ?_⟩
    apply (twistedSectionPushforwardEquiv f L t.val.baseLine.property).injective
    rw [twistedSectionPushforwardEquiv_baseLineIso f L e s.val.baseLine.property,
      lineIsoOfDualIso_dual]
    change a.inv ≫ (s.val.toDirectImage f L).map = (t.val.toDirectImage f L).map
    rw [← ha, Iso.inv_hom_id_assoc]
  · rintro ⟨e, he⟩
    refine ⟨(moduleSheafDualIso _ e).symm, ?_⟩
    have h := twistedSectionPushforwardEquiv_baseLineIso f L e
      s.val.baseLine.property t.val.baseLine.property s.val.section_
    rw [he] at h
    change (moduleSheafDualIso _ e).inv ≫
      twistedSectionPushforwardEquiv f L t.val.baseLine.property t.val.section_ = _
    rw [h]
    change (moduleSheafDualIso _ e).inv ≫ (moduleSheafDualIso _ e).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
    rfl

/-- The base-line orbit supplies an actual section-preserving total-space isomorphism. -/
theorem relativeBaseLineSetoid_implies_sectionSetoid (s t : RelativeSection f L hL)
    (h : (relativeBaseLineSetoid f L hL hV).r s t) :
    (relativeSectionSetoid f L hL).r s t := by
  obtain ⟨e, he⟩ := (relativeBaseLineSetoid_iff_iso f L hL hV s t).mp h
  exact ⟨congr (Iso.refl L) ((pullback f).mapIso e), he⟩

/-- Retained base-line isomorphisms preserve the full relative Cartier zero divisor. -/
theorem relativeSectionToFiber_eq_of_baseLine (s t : RelativeSection f L hL)
    (h : (relativeBaseLineSetoid f L hL hV).r s t) :
    relativeSectionToFiber f L hL s = relativeSectionToFiber f L hL t :=
  (relativeSectionToFiber_eq_iff f L hL s t).mpr
    (relativeBaseLineSetoid_implies_sectionSetoid f L hL hV s t h)

end FLT.Mazur.CartierAbel
