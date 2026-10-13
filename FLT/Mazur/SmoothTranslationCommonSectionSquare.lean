/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationQuotientSectionPullback

/-!
# The original quotient comparison retains common-source regular functions

Restriction to the translation neighborhood does not shrink its common-source
preimage. The section-ring comparison agrees with the original source pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
/-- Pullback of regular functions respects equality of the section domain. -/
theorem sectionPullback_transport {Y Z : Scheme} (g : Y ⟶ Z)
    {U W : Z.Opens} (h : U = W) (s : Γ(Z, U)) :
    g.app W (Z.presheaf.map (eqToHom (congrArg op h)) s) =
      Y.presheaf.map (eqToHom (congrArg (fun A ↦ op (g ⁻¹ᵁ A)) h)) (g.app U s) := by
  subst W
  simp only [eqToHom_refl, Z.presheaf.map_id, Y.presheaf.map_id, CommRingCat.id_apply]

/-- Successive structure-sheaf transports compose on their original sections. -/
theorem sectionMaps_comp {T : TopCat} (F : T.Presheaf CommRingCat)
    {U W Z : (TopologicalSpace.Opens T)ᵒᵖ} (i : U ⟶ W) (j : W ⟶ Z)
    (s : F.obj U) : F.map j (F.map i s) = F.map (i ≫ j) s := by
  rw [F.map_comp]
  rfl

variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

local notation "e" => smoothHilbertEquivalenceRelation f hL
local notation "e'" => variableChartEquivalenceRelation f hL d V c
local notation "p" => variableSourceParameter f hL d V c
local notation "a" => variableSourceInclusion f hL d V c
local notation "j" => smoothTranslationQuotientInclusion f hL d V c

/-- Restricting to the translation neighborhood leaves the common-source domain unchanged. -/
theorem smoothTranslationInclusion_commonOpen
    (O : TopologicalSpace.Opens (Orbit e)) :
    (p).left ⁻¹ᵁ smoothTranslationParameterOpen f hL d V c
      (smoothTranslationInclusionDomain f hL d V c O) =
    (a).left ⁻¹ᵁ (pullOpen e O).val := by
  rw [← smoothTranslationCommonOpen_eq]
  ext x
  change projection e ((a).left x) ∈ smoothTranslationInclusionDomain f hL d V c O ↔
    projection e ((a).left x) ∈ O
  constructor
  · exact fun hx ↦ smoothTranslationInclusionDomain_le f hL d V c O hx
  · intro hx
    refine ⟨smoothTranslationChartToOrbit f hL d V c ((p).left x), ?_, ?_⟩
    · change (smoothTranslationChartToOrbit f hL d V c ((p).left x)).val ∈ O
      rw [smoothTranslationChartToOrbit_parameter]
      exact hx
    · exact congrArg Subtype.val (smoothTranslationChartToOrbit_parameter f hL d V c x)

/-- The actual regular function comparison on the entire common-source domain. -/
theorem smoothTranslationInclusion_commonSection
    (O : TopologicalSpace.Opens (Orbit e))
    (s : (invariantSheaf e).obj.obj (op O)) :
    (variableSourceIntersection f hL d V c).left.presheaf.map
      (eqToHom (congrArg op (smoothTranslationInclusion_commonOpen f hL d V c O)))
      (smoothTranslationChartSectionEquiv f hL d V c
        (smoothTranslationInclusionDomain f hL d V c O)
        (smoothTranslationInvariantSectionRingEquiv f hL d V c
          (smoothTranslationInclusionDomain f hL d V c O)
          (smoothTranslationNeighborhoodOpen_le f hL d V c _)
          ((invariantSheaf e).obj.map
            (homOfLE (smoothTranslationInclusionDomain_le f hL d V c O)).op s))).val =
      (a).left.app (pullOpen e O).val ((invariantInclusion e).hom.app (op O) s) := by
  rw [smoothTranslationInvariantSectionRingEquiv_common,
    smoothTranslationOriginalSectionEquiv_val]
  rw [SchemeEffectiveEpiSections.sectionTransformation_naturality]
  erw [SchemeEffectiveEpiSections.sectionPullback_naturality]
  rw [sectionMaps_comp, sectionMaps_comp]
  change (variableSourceIntersection f hL d V c).left.presheaf.map (𝟙 _) _ = _
  rw [(variableSourceIntersection f hL d V c).left.presheaf.map_id]
  rfl

end FLT.Mazur.HilbertChart
