/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineDescentChart
public import FLT.Mazur.SchemeAffineFlatRefinementThrough

/-!
# Fppf descent charts retaining a prescribed source open

A source affine open lying over an affine base chart factors through an
actual faithfully flat affine descent chart. The factorization into its
covering spectrum is an open immersion and retains the original source map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y W : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p] [IsAffine W]

/-- Retain a prescribed affine open of the original cover inside a descent chart. -/
theorem exists_fppf_chart_through {R : CommRingCat.{u}} (a : Spec R ⟶ X)
    [IsOpenImmersion a] (v : W ⟶ Y) [IsOpenImmersion v]
    (r : W ⟶ Spec R) (w : v ≫ p = r ≫ a) :
    ∃ (C : Chart p) (t : W ⟶ Spec C.coverRing),
      IsOpenImmersion C.base ∧ IsOpenImmersion t ∧ t ≫ C.cover = v := by
  let q := pullback.snd p a
  let l : W ⟶ pullback p a := pullback.lift v r w
  have hl : IsOpenImmersion l := by
    have : IsOpenImmersion (l ≫ pullback.fst p a) := by
      simpa only [l, pullback.lift_fst] using (inferInstance : IsOpenImmersion v)
    exact IsOpenImmersion.of_comp l (pullback.fst p a)
  obtain ⟨Z, hZ, b, t, hb, hfp, hg, hs, ht, htl⟩ :=
    exists_affine_fppf_refinement_through q l
  let := hZ
  let := hb
  let := hfp
  let := hg
  let := hs
  let := ht
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
  refine ⟨⟨R, Γ(Z, ⊤), φ, hφ, a, c, hw⟩, t ≫ Z.isoSpec.hom,
    inferInstance, inferInstance, ?_⟩
  change (t ≫ Z.isoSpec.hom) ≫ (Z.isoSpec.inv ≫ b ≫ pullback.fst p a) = v
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, htl]
  exact pullback.lift_fst v r w

end FLT.Mazur.SchemeAffineDescent
