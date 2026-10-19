/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationNegationCover

/-!
# Constructed negation on the entire modified projective cubic

The actual chart involutions glue by flat-reference contraction uniqueness.
The resulting morphism squares to the identity and retains the original cubic,
coefficient map and both complete invariant chart domains.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassGlobalModification
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
local notation "M" => model W s b3 b4 b6 h3 h4 h6 hs
local notation "c" => contraction W s b3 b4 b6 h3 h4 h6 hs
local notation "C" => modificationNegationCover W s b3 b4 b6 h3 h4 h6 hs
local notation "e" => negationDomainIso W s b3 b4 b6 h3 h4 h6 hs
local notation "i" => negationInclusion W s b3 b4 b6 h3 h4 h6 hs

/-- Negation on either entire original domain, with its target inside the whole model. -/
def globalNegationLocal (b : Bool) : negationDomain W s b3 b4 b6 b ⟶ M :=
  (e b).hom ≫ i b

instance globalNegationLocal_flat (b : Bool) :
    Flat (globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs b) := by
  unfold globalNegationLocal
  infer_instance

/-- Each actual local negative retains the original global cubic map. -/
@[reassoc] theorem globalNegationLocal_contraction (b : Bool) :
    globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs b ≫ c =
      i b ≫ c ≫ integralCurveNegation W := by
  rw [globalNegationLocal, Category.assoc, negationDomainIso_contraction]

/-- The constructed negatives agree on every actual domain intersection. -/
theorem globalNegationLocal_overlap (b d : Bool) :
    pullback.fst (i b) (i d) ≫ globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs b =
      pullback.snd (i b) (i d) ≫ globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs d := by
  apply contraction_ext_of_flat W s b3 b4 b6 h3 h4 h6 hs
    (pullback.snd (i b) (i d) ≫ globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs d)
  simp only [Category.assoc, globalNegationLocal_contraction]
  simpa only [Category.assoc] using
    congrArg (· ≫ c ≫ integralCurveNegation W) (pullback.condition (f := i b) (g := i d))

/-- The regular negative on the complete modified projective cubic. -/
def globalNegation : M ⟶ M :=
  (C).glueMorphisms (globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs)
    (globalNegationLocal_overlap W s b3 b4 b6 h3 h4 h6 hs)

/-- Both complete domain formulas survive global gluing. -/
@[reassoc] theorem negationInclusion_globalNegation (b : Bool) :
    i b ≫ globalNegation W s b3 b4 b6 h3 h4 h6 hs =
      globalNegationLocal W s b3 b4 b6 h3 h4 h6 hs b :=
  (C).ι_glueMorphisms _ _ b

/-- The entire negative lies over the actual original global cubic inverse. -/
@[reassoc] theorem globalNegation_contraction :
    globalNegation W s b3 b4 b6 h3 h4 h6 hs ≫ c = c ≫ integralCurveNegation W := by
  apply (C).hom_ext
  intro b
  change i b ≫ _ = i b ≫ _
  rw [negationInclusion_globalNegation_assoc, globalNegationLocal_contraction]

/-- The complete original integral coefficient map is fixed by negation. -/
@[reassoc] theorem globalNegation_structure :
    globalNegation W s b3 b4 b6 h3 h4 h6 hs ≫ structureMap W s b3 b4 b6 h3 h4 h6 hs =
      structureMap W s b3 b4 b6 h3 h4 h6 hs := by
  rw [structureMap, globalNegation_contraction_assoc, integralCurveNegation_structure]

/-- Applying the constructed whole-model negative twice is exactly the identity. -/
@[reassoc] theorem globalNegation_comp :
    globalNegation W s b3 b4 b6 h3 h4 h6 hs ≫
      globalNegation W s b3 b4 b6 h3 h4 h6 hs = 𝟙 M := by
  apply contraction_ext_of_flat W s b3 b4 b6 h3 h4 h6 hs (𝟙 M)
  rw [Category.assoc, globalNegation_contraction, globalNegation_contraction_assoc,
    integralCurveNegation_comp, Category.comp_id, Category.id_comp]

/-- The whole modified projective cubic has its actual integral negation automorphism. -/
def globalNegationIso : M ≅ M where
  hom := globalNegation W s b3 b4 b6 h3 h4 h6 hs
  inv := globalNegation W s b3 b4 b6 h3 h4 h6 hs
  hom_inv_id := globalNegation_comp W s b3 b4 b6 h3 h4 h6 hs
  inv_hom_id := globalNegation_comp W s b3 b4 b6 h3 h4 h6 hs

end FLT.Mazur.WeierstrassGlobalModification
