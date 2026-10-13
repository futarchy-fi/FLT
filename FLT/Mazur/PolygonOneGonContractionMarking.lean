/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionTorus
public import FLT.Mazur.PolygonMarkedSections

/-!
# The contraction preserves the original retained Cartier marking

The actual point on the retained Laurent component is the entire inverse
image of the target marking. Pullback therefore identifies their Cartier
ideal sheaves on the whole singular source, not just the normalization.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections ProjectiveLineActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

omit [NeZero n] in
/-- The actual unit-marked section survives the contraction with its coordinate unchanged. -/
@[reassoc] theorem section_contraction (a : Kˣ) :
    sectionMap K n p a i ≫ (contraction K n hn p q h i).left =
      sectionMap K 1 (PolygonAtlas.normalization K 1) a 0 := by
  change (unitPoint K a ≫ (torusToComponent K ≫ componentι K n i ≫ p).left) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (fun f ↦ unitPoint K a ≫ f.left) (torus_contraction K n hn p q h i)

/-- The original section is the complete scheme-theoretic inverse image of the target section. -/
theorem section_contraction_square (a : Kˣ) :
    IsPullback (𝟙 (Spec (.of K))) (sectionMap K n p a i)
      (sectionMap K 1 (PolygonAtlas.normalization K 1) a 0)
      (contraction K n hn p q h i).left := by
  have H : IsPullback (𝟙 (Spec (.of K))) (unitPoint K a)
      (unitPoint K a) (𝟙 (MultiplicativeGroupScheme.gm K).left) :=
    by
      change IsPullback (𝟙 _) (unitPoint K a) (unitPoint K a) (𝟙 _)
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact H.paste_vert (contraction_torus_square K n hn p q h i)

/-- The contraction pulls the target marking ideal back to the actual original Cartier ideal. -/
theorem section_contraction_ideal (a : Kˣ) :
    (sectionMap K 1 (PolygonAtlas.normalization K 1) a 0).ker.comap
        (contraction K n hn p q h i).left = (sectionMap K n p a i).ker := by
  let _ := PolygonSeparated.cocone K 1 (by decide)
    (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
    (PolygonAtlas.isPushout K 1 (by decide))
  let _ := FCurve.isClosedImmersion_section (PolygonAtlas.polygon K 1).hom _
    (section_base K 1 (PolygonAtlas.normalization K 1) a 0)
  have H := (section_contraction_square K n hn p q h i a).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

end FLT.Mazur.PolygonOneGonContraction
