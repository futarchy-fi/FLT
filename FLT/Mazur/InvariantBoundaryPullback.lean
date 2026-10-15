/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnvelopeBoundaryIdealSheaf

/-!
# Canonical scheme comparisons for the invariant closed boundary

Equality of the pulled-back boundary ideals constructs an isomorphism of
the actual closed fiber products. It preserves the whole map to the relation
scheme and satisfies identity and composition laws by closed-immersion
monicity. No reduction of the test scheme is performed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
set_option backward.isDefEq.respectTransparency false

private theorem subscheme_eq_ι {Z : Scheme.{u}} (I J : Z.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι =
      I.subschemeι := by
  subst h
  simp

variable {Y X Z : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)
  [IsAffine X] [IsLocallyNoetherian X]
local notation "I" => boundaryIdealSheaf π O
local notation "j" => Scheme.IdealSheafData.subschemeι I

/-- The two closed fiber products are canonically isomorphic over the whole relation. -/
def boundaryPullbackIso (a b : Z ⟶ X) [Smooth a] [Smooth b]
    (h : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O) :
    pullback a j ≅ pullback b j :=
  ((I).comapIso a).symm ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (boundaryIdealSheaf_comap_eq π O a b h)) ≪≫ (I).comapIso b

/-- The comparison retains every relation point and its complete scheme map. -/
@[reassoc]
theorem boundaryPullbackIso_fst (a b : Z ⟶ X) [Smooth a] [Smooth b]
    (h : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O) :
    (boundaryPullbackIso π O a b h).hom ≫ pullback.fst b j = pullback.fst a j := by
  dsimp only [boundaryPullbackIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst,
    subscheme_eq_ι _ _ (boundaryIdealSheaf_comap_eq π O a b h),
    Scheme.IdealSheafData.comapIso_inv_subschemeι]

/-- There is only one comparison retaining the map to the relation scheme. -/
theorem boundaryPullbackIso_unique (a b : Z ⟶ X) [Smooth a] [Smooth b]
    (h : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O)
    (g : pullback a j ⟶ pullback b j)
    (hg : g ≫ pullback.fst b j = pullback.fst a j) :
    g = (boundaryPullbackIso π O a b h).hom := by
  apply (cancel_mono (pullback.fst b j)).mp
  rw [hg, boundaryPullbackIso_fst]

/-- Identity comparison is the actual identity morphism. -/
theorem boundaryPullbackIso_refl (a : Z ⟶ X) [Smooth a] :
    (boundaryPullbackIso π O a a rfl).hom = 𝟙 _ := by
  symm
  exact boundaryPullbackIso_unique π O a a rfl _ (Category.id_comp _)

/-- The comparisons satisfy their scheme cocycle law. -/
theorem boundaryPullbackIso_comp (a b c : Z ⟶ X) [Smooth a] [Smooth b] [Smooth c]
    (hab : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O)
    (hbc : b ⁻¹ᵁ fullFiberInterior π O = c ⁻¹ᵁ fullFiberInterior π O) :
    (boundaryPullbackIso π O a b hab).hom ≫ (boundaryPullbackIso π O b c hbc).hom =
      (boundaryPullbackIso π O a c (hab.trans hbc)).hom := by
  apply boundaryPullbackIso_unique
  rw [Category.assoc, boundaryPullbackIso_fst, boundaryPullbackIso_fst]

end FLT.Mazur.SchemeOpenEnvelope
