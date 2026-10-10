/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatStructureSectionComplex
public import FLT.Mazur.SchemeRelativeNilpotentSections

/-!
# A residue-complex criterion for actual relative functions

For a pointed flat family over an affine Artinian base, exactness of the actual
affine-cover complex over each residue field implies that structural pullback
is bijective. Flatness of the cover terms is proved geometrically. Identifying
these residue complexes with the geometric fiber complexes remains necessary
before applying the criterion from connectedness and reducedness of the fibers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.ArtinianRelativeSectionCriterion
open Chow PolygonStructureInclusion ArtinianSectionKernel
variable {X S : Scheme} (f : X ⟶ S)

/-- Structural pullback as a map into the original base-linear global sections. -/
def scalarSections : Γ(S, ⊤) →ₗ[Γ(S, ⊤)] baseSections (structureModule X) f.appTop.hom ⊤ where
  toFun := f.appTop
  map_add' := map_add f.appTop.hom
  map_smul' r a := by
    change f.appTop (r * a) = X.presheaf.map (𝟙 (op ⊤)) (f.appTop r) * f.appTop a
    rw [X.presheaf.map_id, ConcreteCategory.id_apply, map_mul]

/-- Scalar sections retain the original ring pullback. -/
lemma scalarSections_apply (a : Γ(S, ⊤)) : scalarSections f a = f.appTop a := rfl

/-- The original scheme section evaluates global sections linearly over base functions. -/
def evaluation (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) :
    baseSections (structureModule X) f.appTop.hom ⊤ →ₗ[Γ(S, ⊤)] Γ(S, ⊤) where
  toFun := s.appTop
  map_add' := map_add s.appTop.hom
  map_smul' r a := by
    change s.appTop (X.presheaf.map (𝟙 (op ⊤)) (f.appTop r) *
      (show Γ(X, ⊤) from a)) = r * s.appTop a
    rw [X.presheaf.map_id, ConcreteCategory.id_apply, map_mul,
      SchemeRelativeNilpotentSections.evaluation_pullback f s hs]

/-- The linear evaluation is a retraction because the original scheme maps form a section. -/
lemma evaluation_scalarSections (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) :
    (evaluation f s hs).comp (scalarSections f) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  exact SchemeRelativeNilpotentSections.evaluation_pullback f s hs a

variable [IsAffine S] [Flat f] [X.IsSeparated] [IsArtinianRing Γ(S, ⊤)]
  {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hA : ∀ i, IsAffineOpen (U i))

include hU hA in
/-- Residue-field exactness of the affine-cover complex proves the actual global comparison. -/
theorem appTop_bijective (s : S ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hres : ∀ (I : Ideal Γ(S, ⊤)) [I.IsMaximal],
      Function.Exact
        ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor
          (Γ(S, ⊤) ⧸ I))
        ((baseDifference (structureModule X) f.appTop.hom U).lTensor (Γ(S, ⊤) ⧸ I))) :
    Function.Bijective f.appTop := by
  let _ := FlatStructureSectionComplex.overlapProduct_flat f U hA
  exact bijective_of_residue_exact (structureModule X) f.appTop.hom U hU
    (scalarSections f) (evaluation f s hs) (evaluation_scalarSections f s hs) hres

end FLT.Mazur.ArtinianRelativeSectionCriterion
