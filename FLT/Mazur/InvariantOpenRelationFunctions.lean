/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenRelationDiagram
public import FLT.Mazur.RelativeRelationInvariantSectionRings

/-!
# Actual function coordinates for restricted full relations

The full endpoint equalizer on the restricted scheme is identified with the
original functions on the invariant open. For orbit opens this gives the
actual invariant-sheaf sections, retaining their original source inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.InvariantOpenRelationDiagram
open SchemeFunctionGroundChange RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} {A D : Over S} (p q : D ⟶ A)
  (U : A.left.Opens) (hU : p.left ⁻¹ᵁ U = q.left ⁻¹ᵁ U)
attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

/-- Function coordinates on the actual restricted source scheme. -/
def sourceFunctions : Γ(A.left, U) ≃+* Γ((source U).left, ⊤) :=
  U.topIso.symm.commRingCatIsoToRingEquiv

/-- The first restricted endpoint is the original pullback in open coordinates. -/
theorem fst_function (a : Γ(A.left, U)) :
    sectionMap (fst p U) (sourceFunctions U a) =
      (p.left ⁻¹ᵁ U).topIso.inv (p.left.app U a) := by
  change (p.left.resLE U _ le_rfl).appTop (U.topIso.inv a) = _
  simp only [Scheme.Hom.resLE_app_top, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply, Scheme.Hom.appLE_eq_app]

/-- The second endpoint keeps its independent pullback and its exact open transport. -/
theorem snd_function (a : Γ(A.left, U)) :
    sectionMap (snd p q U hU) (sourceFunctions U a) =
      (p.left ⁻¹ᵁ U).topIso.inv (q.left.appLE U _ hU.le a) := by
  change (q.left.resLE U _ hU.le).appTop (U.topIso.inv a) = _
  simp only [Scheme.Hom.resLE_app_top, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

/-- Both complete endpoint equations are retained on the original invariant domain. -/
theorem invariant_iff (a : Γ(A.left, U)) :
    sourceFunctions U a ∈ AlgHom.equalizer (sectionMap (fst p U))
      (sectionMap (snd p q U hU)) ↔
      a ∈ originalInvariantSections (p := p) (q := q) U hU := by
  change sectionMap (fst p U) (sourceFunctions U a) =
      sectionMap (snd p q U hU) (sourceFunctions U a) ↔ _
  rw [fst_function, snd_function]
  exact (p.left ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.injective.eq_iff

/-- All invariant functions, with no finite generation hypothesis, in restricted coordinates. -/
def invariantFunctions : originalInvariantSections (p := p) (q := q) U hU ≃+*
    AlgHom.equalizer (sectionMap (fst p U)) (sectionMap (snd p q U hU)) :=
  RingEquiv.ofBijective
    (((sourceFunctions U).toRingHom.comp
      (originalInvariantSections (p := p) (q := q) U hU).subtype).codRestrict _
      (fun a ↦ (invariant_iff p q U hU a.val).mpr a.property)) (by
    constructor
    · intro a b hab
      exact Subtype.ext ((sourceFunctions U).injective (congrArg Subtype.val hab))
    · intro a
      refine ⟨⟨(sourceFunctions U).symm a.val, ?_⟩, ?_⟩
      · apply (invariant_iff p q U hU _).mp
        simpa only [RingEquiv.apply_symm_apply] using a.property
      · exact Subtype.ext ((sourceFunctions U).apply_symm_apply a.val))

/-- The restricted comparison retains the original source function exactly. -/
theorem invariantFunctions_val
    (a : originalInvariantSections (p := p) (q := q) U hU) :
    (invariantFunctions p q U hU a).val = sourceFunctions U a.val := rfl

variable {p q} (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))

/-- Actual sections on any orbit open in full restricted scheme-relation coordinates. -/
def orbitFunctions : (invariantSheaf e).obj.obj (op W) ≃+*
    AlgHom.equalizer (sectionMap (fst p (pullOpen e W).val))
      (sectionMap (snd p q (pullOpen e W).val (pullOpen_preimage_eq e W))) :=
  (invariantSectionRingEquiv e W).trans
    (invariantFunctions p q (pullOpen e W).val (pullOpen_preimage_eq e W))

/-- Orbit-open coordinates preserve the actual invariant-sheaf inclusion. -/
theorem orbitFunctions_val (a : (invariantSheaf e).obj.obj (op W)) :
    (orbitFunctions e W a).val =
      sourceFunctions (pullOpen e W).val ((invariantInclusion e).hom.app (op W) a) := rfl

end FLT.Mazur.InvariantOpenRelationDiagram
