/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNegationOverlap

/-!
# Constructed negation on every entire finite projective model

Glue the actual involutions on the invariant cover. Their squares prove
involutivity on the entire scheme, and their original cubic contractions
retain the initially chosen coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "M" => finiteGlobalModel hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "i" => finiteNegationInclusion hπ data j hj
local notation "e" => finiteNegationDomainIso hπ data j hj

local notation "C" => finiteNegationCover hπ data j hj

/-- Both complete invariant domain negatives square to the identity. -/
@[reassoc] theorem finiteNegationDomainIso_comp (b : Bool) :
    (e b).hom ≫ (e b).hom = 𝟙 _ := by
  cases b
  · exact finiteWholeNegationIso_comp hπ data j hj
  · change Spec.map (CommRingCat.ofHom (infinityNegationEnd W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (infinityNegationEnd W).toRingHom) = 𝟙 _
    rw [← Spec.map_comp]
    have h := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (infinityNegationEnd_comp W)
    exact h.trans (by simp)

/-- The regular negative on the entire finite projective model. -/
def finiteGlobalNegation : M ⟶ M :=
  (C).glueMorphisms (finiteGlobalNegationLocal hπ data j hj)
    (finiteGlobalNegationLocal_overlap hπ data j hj)

/-- Each complete invariant domain retains its original negative after gluing. -/
@[reassoc] theorem finiteNegationInclusion_negation (b : Bool) :
    i b ≫ finiteGlobalNegation hπ data j hj = (e b).hom ≫ i b :=
  (C).ι_glueMorphisms _ _ b

/-- The entire projective negative retains the originally chosen cubic inverse. -/
@[reassoc] theorem finiteGlobalNegation_contraction :
    finiteGlobalNegation hπ data j hj ≫ c = c ≫ integralCurveNegation W := by
  apply (C).hom_ext
  intro b
  change i b ≫ _ = i b ≫ _
  rw [finiteNegationInclusion_negation_assoc, finiteNegationDomainIso_contraction]

/-- The negative fixes the actual original coefficient morphism. -/
@[reassoc] theorem finiteGlobalNegation_structure :
    finiteGlobalNegation hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      finiteGlobalStructure hπ data j hj := by
  rw [finiteGlobalStructure, finiteGlobalNegation_contraction_assoc,
    integralCurveNegation_structure]

/-- The constructed whole-model negative squares to the identity on every component. -/
@[reassoc] theorem finiteGlobalNegation_comp :
    finiteGlobalNegation hπ data j hj ≫ finiteGlobalNegation hπ data j hj = 𝟙 M := by
  apply (C).hom_ext
  intro b
  change i b ≫ _ = i b ≫ _
  rw [finiteNegationInclusion_negation_assoc,
    finiteNegationInclusion_negation, finiteNegationDomainIso_comp_assoc,
    Category.comp_id]

/-- Every entire finite projective model has a constructed integral negation automorphism. -/
def finiteGlobalNegationIso : M ≅ M where
  hom := finiteGlobalNegation hπ data j hj
  inv := finiteGlobalNegation hπ data j hj
  hom_inv_id := finiteGlobalNegation_comp hπ data j hj
  inv_hom_id := finiteGlobalNegation_comp hπ data j hj

end FLT.Mazur.WeierstrassDividedDepth
