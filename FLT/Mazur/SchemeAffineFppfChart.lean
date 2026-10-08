/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineDescentChart
public import FLT.Mazur.SchemeAffineFlatRefinement

/-!
# Faithfully flat affine charts of an actual fppf morphism

Base change to an affine open, refine the resulting fppf map by a finite
union of affine opens, and pass to spectra. This constructs the chart
square and proves faithful flatness of its coordinate-ring map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

/-- Every affine open of the base admits a faithfully flat affine descent chart. -/
theorem exists_fppf_chart {R : CommRingCat.{u}} (a : Spec R ⟶ X) [IsOpenImmersion a] :
    ∃ (S : CommRingCat.{u}) (φ : R ⟶ S) (c : Spec S ⟶ Y),
      φ.hom.FaithfullyFlat ∧ Spec.map φ ≫ a = c ≫ p ∧
        Flat c ∧ LocallyOfFinitePresentation c := by
  let q := pullback.snd p a
  obtain ⟨Z, hZ, b, hb, hfp, hg, hs⟩ := exists_affine_fppf_refinement q
  let := hZ
  let := hb
  let := hfp
  let := hg
  let := hs
  let g : Spec Γ(Z, ⊤) ⟶ Spec R := Z.isoSpec.inv ≫ (b ≫ q)
  let c : Spec Γ(Z, ⊤) ⟶ Y := Z.isoSpec.inv ≫ b ≫ pullback.fst p a
  let φ := Spec.preimage g
  have hφ : φ.hom.FaithfullyFlat := by
    apply (flat_and_surjective_SpecMap_iff φ).mp
    dsimp only [φ]
    rw [Spec.map_preimage]
    exact ⟨inferInstanceAs (Flat g), inferInstanceAs (Surjective g)⟩
  have hw : Spec.map φ ≫ a = c ≫ p := by
    dsimp only [φ]
    rw [Spec.map_preimage]
    dsimp only [g, c, q]
    simp only [Category.assoc, pullback.condition]
  exact ⟨Γ(Z, ⊤), φ, c, hφ, hw, inferInstance, inferInstance⟩

/-- A chosen actual affine chart over a prescribed affine open of the base. -/
def fppfChart {R : CommRingCat.{u}} (a : Spec R ⟶ X) [IsOpenImmersion a] : Chart p :=
  { baseRing := R
    coverRing := (exists_fppf_chart p a).choose
    ringMap := (exists_fppf_chart p a).choose_spec.choose
    faithfullyFlat := (exists_fppf_chart p a).choose_spec.choose_spec.choose_spec.1
    base := a
    cover := (exists_fppf_chart p a).choose_spec.choose_spec.choose
    square := (exists_fppf_chart p a).choose_spec.choose_spec.choose_spec.2.1 }

/-- The constructed chart retains the prescribed affine base map exactly. -/
@[simp]
lemma fppfChart_base {R : CommRingCat.{u}} (a : Spec R ⟶ X) [IsOpenImmersion a] :
    (fppfChart p a).base = a := rfl

instance fppfChart_base_isOpenImmersion {R : CommRingCat.{u}} (a : Spec R ⟶ X)
    [IsOpenImmersion a] : IsOpenImmersion (fppfChart p a).base := by
  rw [fppfChart_base]
  infer_instance

instance fppfChart_cover_flat {R : CommRingCat.{u}} (a : Spec R ⟶ X)
    [IsOpenImmersion a] : Flat (fppfChart p a).cover :=
  (exists_fppf_chart p a).choose_spec.choose_spec.choose_spec.2.2.1

instance fppfChart_cover_locallyOfFinitePresentation {R : CommRingCat.{u}}
    (a : Spec R ⟶ X) [IsOpenImmersion a] :
    LocallyOfFinitePresentation (fppfChart p a).cover :=
  (exists_fppf_chart p a).choose_spec.choose_spec.choose_spec.2.2.2

end FLT.Mazur.SchemeAffineDescent
