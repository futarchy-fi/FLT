/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProductTranslationNorm
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Compatible local norms over a possibly nonaffine source

Pull an actual global envelope section to each affine test over the source.
Finite-free envelope norms agree under every affine refinement, so they give
compatible local regular functions without a global affine coaction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation AffineProductTranslationNorm SchemeEffectiveEpiSections
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (Y V : Over (Spec (.of R))) [IsAffine V.left]
/-- The original translation section algebra. -/
local instance translationAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((prod Y V).left, ⊤))

/-- Restrict the actual envelope section before taking its finite-free affine norm. -/
def localNorm {T : Over (Spec (.of R))} [IsAffine T.left] (t : T ⟶ Y) : Γ(T.left, ⊤) :=
  envelopeNorm T V b ((prod.map t (𝟙 V)).left.appTop s)

/-- Local norms agree under all affine tests, without assuming the source affine. -/
theorem localNorm_comp {T Q : Over (Spec (.of R))} [IsAffine T.left] [IsAffine Q.left]
    (t : T ⟶ Y) (q : Q ⟶ T) :
    localNorm Y V b s (q ≫ t) = q.left.appTop (localNorm Y V b s t) := by
  have he : prod.map (q ≫ t) (𝟙 V) = prod.map q (𝟙 V) ≫ prod.map t (𝟙 V) := by
    apply prod.hom_ext <;> simp only [Category.assoc, prod.map_fst,
      prod.map_snd, Category.comp_id, prod.map_fst_assoc]
  dsimp only [localNorm]
  rw [he, Over.comp_left, Scheme.Hom.comp_appTop]
  exact envelopeNorm_natural T Q V b q _

/-- Represent the norm on an affine test by an actual morphism to the function scheme. -/
def localNormMap {T : Over (Spec (.of R))} [IsAffine T.left] (t : T ⟶ Y) :
    T.left ⟶ functionScheme :=
  (functionEquiv T.left).symm (localNorm Y V b s t)

/-- Local representing morphisms commute with every affine refinement. -/
@[reassoc]
theorem localNormMap_comp {T Q : Over (Spec (.of R))}
    [IsAffine T.left] [IsAffine Q.left] (t : T ⟶ Y) (q : Q ⟶ T) :
    q.left ≫ localNormMap Y V b s t = localNormMap Y V b s (q ≫ t) := by
  apply (functionEquiv Q.left).injective
  rw [functionEquiv_comp]
  simp only [localNormMap, Equiv.apply_symm_apply, localNorm_comp]

end FLT.Mazur.SchemeTranslationNorm
