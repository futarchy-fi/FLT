/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleChartGeneratorRatios
public import FLT.Mazur.FiniteSectionProjectivePresentation
public import FLT.Mazur.RelativeAmpleSectionComparison

/-!
# The proper ample converse over arbitrary bases

Local chart algebra generators extend after powers and define an immersion.
Properness makes this immersion closed, giving the project's projective
presentation predicate from section ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionCover ProjectiveSpace
variable {X : Scheme} {R : Type} [CommRing R] (f : X ⟶ Spec (.of R))

/-- The coefficient ring map on an affine source open is of finite type. -/
theorem sectionChartScalars_finiteType [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (sectionChartScalars (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) U).FiniteType := by
  have h := f.finiteType_appLE (isAffineOpen_top _) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  have h' := h.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective)
  convert h' using 1
  ext a
  simp only [sectionChartScalars, RingHom.comp_apply, Scheme.Hom.appTop,
    Scheme.Hom.appLE, CommRingCat.comp_apply]
  rfl

/-- On a proper scheme over an arbitrary affine base, an ample sheaf has a very ample power. -/
theorem AmpleLineBundle.exists_power_presentation [IsProper f] {L : X.Modules}
    (hL : AmpleLineBundle L) :
    ∃ m > 0, Nonempty (VeryAmplePresentation f (tensorPower L m)) := by
  obtain ⟨ι, hι, d, hd, s, haff, hcover⟩ := hL.common_degree_section_cover
  let := hι
  let M := tensorPower L d
  let r := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  obtain ⟨G, D, hD, σ, hopen, hG, hσ⟩ := sectionCover_algebra_generators
    (hL.2.1.tensorPower d) s haff hcover
    (fun j ↦ sectionChartScalars r (chart s j))
    (fun j ↦ sectionChartScalars_finiteType f (chart s j) (haff j))
  obtain ⟨p⟩ := finiteSection_presentation f (chart s) haff hcover
    (fun j ↦ tensorPowerSection M ⊤ (s j) D) hopen G σ hG hσ
  exact ⟨d * D, Nat.mul_pos hd hD, ⟨p.ofIso (tensorPowerMulIso L d D).symm⟩⟩

/-- Relative section ampleness of a proper morphism gives closed projective power presentations. -/
theorem RelativelyAmpleLineBundle.relativeAmple {S : Scheme} {f : X ⟶ S} [IsProper f]
    {L : X.Modules} (hL : RelativelyAmpleLineBundle f L) : RelativeAmple f L := by
  intro U hU
  have : IsProper (f ∣_ U) := inferInstance
  have : IsProper ((f ∣_ U) ≫ hU.isoSpec.hom) := inferInstance
  obtain ⟨m, hm, ⟨p⟩⟩ := (hL.2.2 U hU).exists_power_presentation
    ((f ∣_ U) ≫ hU.isoSpec.hom)
  exact ⟨m, hm, ⟨p.ofIso (tensorPowerRestrictIso L (f ⁻¹ᵁ U).ι m)⟩⟩

/-- On proper morphisms the two ample predicates agree for invertible sheaves. -/
theorem relativeAmple_iff_relativelyAmpleLineBundle {S : Scheme} {f : X ⟶ S}
    [IsProper f] {L : X.Modules} (hL : LocallyFreeRankOne L) :
    RelativeAmple f L ↔ RelativelyAmpleLineBundle f L :=
  ⟨fun h ↦ h.relativelyAmpleLineBundle hL, RelativelyAmpleLineBundle.relativeAmple⟩

/-- Closed power presentations are precisely properness together with section ampleness. -/
theorem relativeAmple_iff_proper_and_relativelyAmple {S : Scheme} {f : X ⟶ S}
    {L : X.Modules} (hL : LocallyFreeRankOne L) :
    RelativeAmple f L ↔ IsProper f ∧ RelativelyAmpleLineBundle f L := by
  refine ⟨fun h ↦ ⟨h.isProper, h.relativelyAmpleLineBundle hL⟩, ?_⟩
  rintro ⟨hf, h⟩
  let := hf
  exact h.relativeAmple

end FLT.Mazur.FCurve
