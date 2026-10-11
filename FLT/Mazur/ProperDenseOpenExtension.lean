/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSectionGluing

/-!
# Extending maps from dense opens to proper targets

Valuation stalks on an integral separated source extend a generic map to the
pullback of a proper target. Separatedness identifies the extension with the
original morphism on its entire dense open domain.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A generic map into a proper target extends over a source with valuation stalks. -/
theorem exists_generic_extension_of_valuation_stalks
    {S X Z : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (q : X ⟶ S) (r : Z ⟶ S) [IsProper r]
    (g : Spec X.functionField ⟶ Z)
    (hg : g ≫ r = X.fromSpecStalk (genericPoint X) ≫ q) :
    ∃ f : X ⟶ Z, f ≫ r = q ∧ X.fromSpecStalk (genericPoint X) ≫ f = g := by
  let P : Over X := Over.mk (pullback.snd r q)
  let _ : IsProper P.hom := inferInstanceAs (IsProper (pullback.snd r q))
  let x : Points P (X.fromSpecStalk (genericPoint X)) :=
    Over.homMk (pullback.lift g (X.fromSpecStalk (genericPoint X)) hg)
      (by exact pullback.lift_snd _ _ _)
  obtain ⟨y, hy, _⟩ := Sections.existsUnique_of_valuation_stalks X P x
  refine ⟨y.left ≫ pullback.fst r q, ?_, ?_⟩
  · have hyq : y.left ≫ pullback.snd r q = 𝟙 X := Over.w y
    rw [Category.assoc, pullback.condition, ← Category.assoc, hyq, Category.id_comp]
  · have hy' := congrArg (fun z ↦ z.left) hy
    change X.fromSpecStalk (genericPoint X) ≫ y.left =
      pullback.lift g (X.fromSpecStalk (genericPoint X)) hg at hy'
    simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun z ↦ z ≫ pullback.fst r q) hy'

/-- The extension is unique and agrees with the original map on its whole dense open. -/
theorem existsUnique_denseOpen_extension_of_valuation_stalks
    {S X Z : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (q : X ⟶ S) (r : Z ⟶ S) [IsProper r]
    (U : X.Opens) (hU : Dense (U : Set X)) (g : U.toScheme ⟶ Z)
    (hg : g ≫ r = U.ι ≫ q) :
    ∃! f : X ⟶ Z, f ≫ r = q ∧ U.ι ≫ f = g := by
  have hη : genericPoint X ∈ U :=
    (genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec
  let t := U.fromSpecStalkOfMem (genericPoint X) hη
  have ht : t ≫ U.ι = X.fromSpecStalk (genericPoint X) :=
    Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  let _ : IsDominant (X.fromSpecStalk (genericPoint X)) := genericStalk_isDominant X
  have : IsDominant (t ≫ U.ι) := ht.symm ▸ inferInstance
  let _ : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t U.ι
  obtain ⟨f, hf, hfη⟩ := exists_generic_extension_of_valuation_stalks q r (t ≫ g)
    (by rw [Category.assoc, hg, ← Category.assoc, ht])
  have hfg : U.ι ≫ f = g := by
    apply ext_of_isDominant_of_isSeparated r (by rw [Category.assoc, hf, hg]) t
    rw [← Category.assoc, ht, hfη]
  refine ⟨f, ⟨hf, hfg⟩, ?_⟩
  intro f' hf'
  let _ : IsDominant U.ι := Opens.isDominant_ι hU
  exact ext_of_isDominant_of_isSeparated r (hf'.1.trans hf.symm) U.ι
    (hf'.2.trans hfg.symm)

end FLT.Mazur
