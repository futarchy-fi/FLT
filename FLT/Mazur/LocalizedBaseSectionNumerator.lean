/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalSectionBaseChange
public import FLT.Mazur.ModuleGlobalSectionPullback
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Numerators for sections after localized base change

Flat global-section base change identifies localized sections with a tensor
product. Every section therefore becomes the pullback of an original section
after multiplication by one denominator from the specified base localization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped ChangeOfRings TensorProduct

namespace FLT.Mazur.FlatGlobalSectionBaseChange

open OpenModuleSectionScalars FCurve

variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

include h in
/-- A section after localized base change has an actual original global numerator. -/
theorem exists_localized_section_numerator (W : Submonoid Γ(S, ⊤))
    (hW : let _ := g.appTop.hom.toAlgebra; IsLocalization W Γ(T, ⊤))
    (s : Γ((pullback p).obj M, ⊤)) :
    ∃ (r : W) (t : Γ(M, ⊤)),
      pullGlobal p M t = q.appTop (g.appTop r.val) • s := by
  let _ := g.appTop.hom.toAlgebra
  let _ := hW
  let e := sectionsIso h M
  let z : Γ(T, ⊤) ⊗[Γ(S, ⊤)] openSections f M ⊤ :=
    e.inv (show openSections q ((pullback p).obj M) ⊤ from s)
  obtain ⟨⟨t, r⟩, ht⟩ := IsLocalizedModule.surj W
    (TensorProduct.mk Γ(S, ⊤) Γ(T, ⊤) (openSections f M ⊤) 1) z
  refine ⟨r, t, ?_⟩
  have ht' : g.appTop r.val • z =
      (1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] t := by
    change (algebraMap Γ(S, ⊤) Γ(T, ⊤)) r.val •
      z = _
    rw [algebraMap_smul]
    exact ht
  have he := congrArg e.hom ht'
  rw [_root_.map_smul, show e.hom z = (show openSections q ((pullback p).obj M) ⊤ from s) from
    ConcreteCategory.congr_hom e.inv_hom_id s, sectionsIso_tmul, one_smul] at he
  change (P.presheaf.map (homOfLE (show (⊤ : P.Opens) ≤ ⊤ from le_top)).op
    (q.appTop (g.appTop r.val))) • s = pullGlobal p M t at he
  change (P.presheaf.map (𝟙 _)) (q.appTop (g.appTop r.val)) • s = _ at he
  rw [P.presheaf.map_id, ConcreteCategory.id_apply] at he
  exact he.symm

end FLT.Mazur.FlatGlobalSectionBaseChange
