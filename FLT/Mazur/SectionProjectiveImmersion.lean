/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionProjectiveOver
public import FLT.Mazur.ModuleSectionProjectiveOOne
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Immersion criterion for the morphism of a generating family

It suffices that a collection of affine generator charts covers the source
and that their actual ratio ring maps are surjective. Properness then gives
a closed projective presentation of the supplied sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (L : X.Modules) {R : Type} [CommRing R] (n : ℕ)
    (t : Fin (n + 1) → Γ(L, ⊤))

/-- Surjectivity of the chart ring map makes the local projective map an immersion. -/
theorem sectionProjectiveChartMorphism_isImmersion (i : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionGeneratorOpen L (t i)) (hU : IsAffineOpen U) (r : R →+* Γ(X, U))
    (hr : Function.Surjective (sectionProjectiveChartRingMap L n t i U hi r)) :
    IsImmersion (sectionProjectiveChartMorphism L n t i U hi r) := by
  let : IsAffine U.toScheme := hU
  have : IsIso U.toScheme.toSpecΓ := inferInstance
  have : IsImmersion U.toScheme.toSpecΓ := inferInstance
  let φ := U.topIso.inv.hom.comp (sectionProjectiveChartRingMap L n t i U hi r)
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso U.topIso.inv).surjective.comp hr
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have : IsImmersion (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  have : IsImmersion (Spec.map (CommRingCat.ofHom φ) ≫ chartMap R (Fin (n + 1)) i) :=
    IsImmersion.comp _ _
  exact IsImmersion.comp U.toScheme.toSpecΓ _

/-- Surjective chart coordinates on a subcover suffice for a projective immersion. -/
theorem sectionProjectiveMorphism_isImmersion
    (ht : ⨆ i, sectionGeneratorOpen L (t i) = ⊤) (r : R →+* Γ(X, ⊤))
    (good : Set (Fin (n + 1)))
    (hgood : ∀ x : X, ∃ i ∈ good, x ∈ sectionGeneratorOpen L (t i))
    (haff : ∀ i ∈ good, IsAffineOpen (sectionGeneratorOpen L (t i)))
    (hsurj : ∀ i ∈ good, Function.Surjective
      (sectionProjectiveChartRingMap L n t i (sectionGeneratorOpen L (t i)) le_rfl
        (sectionChartScalars r (sectionGeneratorOpen L (t i))))) :
    IsImmersion (sectionProjectiveMorphism L n t ht r) := by
  let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun i hi f hf ↦ by
      let := hi
      let := hf
      exact IsImmersion.comp f i⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion)
  intro x
  obtain ⟨i, hi, hx⟩ := hgood x
  refine ⟨chart R (Fin (n + 1)) i, ?_, ?_⟩
  · have hx' : x ∈ sectionProjectiveMorphism L n t ht r ⁻¹ᵁ chart R (Fin (n + 1)) i := by
      rwa [sectionProjectiveMorphism_preimage_chart]
    exact hx'
  · rw [sectionProjectiveMorphism_preimage_chart, sectionGeneratorOpen_ι_projectiveMorphism]
    exact sectionProjectiveChartMorphism_isImmersion L n t i _ le_rfl (haff i hi) _ (hsurj i hi)

/-- Properness upgrades the section immersion to a closed projective presentation. -/
def sectionVeryAmplePresentation (ht : ⨆ i, sectionGeneratorOpen L (t i) = ⊤)
    (f : X ⟶ Spec (.of R)) [IsProper f]
    [IsImmersion (sectionProjectiveMorphism L n t ht
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom))] :
    VeryAmplePresentation f L := by
  let r := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let g := sectionProjectiveMorphism L n t ht r
  have hover : g ≫ baseProjection R _ = f := sectionProjectiveMorphism_baseProjection L n t ht f
  have : IsProper (g ≫ baseProjection R _) := hover ▸ inferInstance
  have : IsProper g := IsProper.of_comp g (baseProjection R _)
  exact ⟨n, g, IsClosedImmersion.of_isPreimmersion g g.isClosedMap.isClosed_range,
    hover, (sectionProjectiveOOneIso L n t ht r).symm⟩

end FLT.Mazur.FCurve
