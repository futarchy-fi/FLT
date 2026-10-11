/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealConditionAcyclic
public import FLT.Mazur.SectionConditionDimension
public import FLT.Mazur.FiniteSchemeLineCohomology
public import FLT.Mazur.ProperCoherentCohomology
public import FLT.Mazur.CurveGenus

/-!
# Dimension loss from a finite ideal condition

The quotient term of the actual ideal sequence has dimension equal to the
finite closed-scheme length. In particular, a quotient isomorphic to the base
field imposes precisely one condition whenever the original restriction is nonzero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve
open Scheme.Modules ModuleSheafTensor

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (.of k)) [IsProper f]
  (I : X.IdealSheafData) {L : X.Modules} (hL : LocallyFreeRankOne L)

include hL in
/-- The actual tensor quotient has dimension equal to the full finite scheme length. -/
theorem idealLineCondition_quotient_finrank [IsFinite (I.subschemeι ≫ f)] :
    Module.finrank k (ModuleScalarH f (idealLineCondition I (L := L)).X₃ 0) =
      finiteSchemeLength (I.subschemeι ≫ f) := by
  let e := LineStructureProjection.iso I.subschemeι L hL
  exact ((moduleScalarHFunctor f 0).mapIso e).toLinearEquiv.finrank_eq.trans
    (finiteClosed_line_h0_finrank I.subschemeι f (hL.pullback I.subschemeι))

omit [IsProper f] in
/-- A closed quotient isomorphic to the base field has length exactly one. -/
theorem finiteSchemeLength_eq_one_of_isIso [IsIso f] : finiteSchemeLength f = 1 := by
  apply finrank_H0_of_constantGlobalSections f
  change Function.Bijective (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  exact ConcreteCategory.bijective_of_isIso _

include hL in
/-- A nonzero original restriction to a rational subscheme cuts H⁰ by one. -/
theorem idealLine_acyclic_rank_drop_one [IsIso (I.subschemeι ≫ f)]
    [Subsingleton (ModuleScalarH f L 1)] (s : Γ(L, ⊤))
    (hs : pullGlobal I.subschemeι L s ≠ 0) :
    Subsingleton (ModuleScalarH f (tensor (idealModule I) L) 1) ∧
      Module.finrank k (ModuleScalarH f (tensor (idealModule I) L) 0) + 1 =
        Module.finrank k (ModuleScalarH f L 0) := by
  let S := idealLineCondition I (L := L)
  let e := leftUnitor L
  let c : ModuleScalarH f S.X₂ 0 ≃ₗ[k] ModuleScalarH f L 0 :=
    ((moduleScalarHFunctor f 0).mapIso e).toLinearEquiv
  let _ := hL.isFinitePresentation
  let _ : Module.Finite k (ModuleScalarH f L 0) :=
    proper_coherent_hasFiniteCohomology f L 0
  let _ : Module.Finite k (ModuleScalarH f S.X₂ 0) := Module.Finite.equiv c.symm
  let _ : Subsingleton (ModuleH L 1) :=
    inferInstanceAs (Subsingleton (ModuleScalarH f L 1))
  let _ : Subsingleton (ModuleScalarH f S.X₂ 1) := moduleH_subsingleton_of_iso e 1
  have hr : Module.finrank k (ModuleScalarH f S.X₃ 0) = 1 :=
    (idealLineCondition_quotient_finrank f I hL).trans
      (finiteSchemeLength_eq_one_of_isIso (I.subschemeι ≫ f))
  let t := e.inv.app ⊤ s
  have ht : S.g.app ⊤ t ≠ 0 := by
    intro hz
    have h := congrArg (fun a ↦ a.app ⊤ t) (idealLineCondition_projection I hL)
    have he : e.hom.app ⊤ t = s :=
      ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app ⊤) e.inv_hom_id) s
    have hh : (LineStructureProjection.iso I.subschemeι L hL).hom.app ⊤ (S.g.app ⊤ t) =
        pullGlobal I.subschemeι L (e.hom.app ⊤ t) := h
    rw [hz, map_zero, he] at hh
    exact hs hh.symm
  obtain ⟨hz, hd⟩ := kernel_acyclic_rank_drop_one f S (idealLineCondition_shortExact I hL)
    hr t ht
  exact ⟨hz, hd.trans c.finrank_eq⟩

end FLT.Mazur.FCurve
