/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFiberTensorComplex

/-!
# Actual relative functions over an Artinian affine base

For a pointed flat proper family with geometrically connected reduced fibers,
the original structural pullback on global functions is bijective over an
Artinian affine base. Residue exactness is proved from the actual fibers;
the total space and the base are allowed to be nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.ArtinianProperRelativeFunctions
open Chow PolygonStructureInclusion ArtinianSectionKernel ArtinianRelativeSectionCriterion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsAffine S] [IsArtinianRing Γ(S, ⊤)]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs in
/-- The original affine-cover complex is exact with every coefficient module. -/
theorem cover_exact {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hA : ∀ i, IsAffineOpen (U i))
    (B : Type) [AddCommGroup B] [Module Γ(S, ⊤) B] :
    Function.Exact
      ((chartMap (structureModule X) f.appTop.hom U (scalarSections f)).lTensor B)
      ((baseDifference (structureModule X) f.appTop.hom U).lTensor B) := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := FlatStructureSectionComplex.overlapProduct_flat f U hA
  exact exact_arbitrary_coefficients (structureModule X) f.appTop.hom U
    (scalarSections f) (ProperFiberTensorComplex.residue_exact f U hU hA s hs) B

include s hs in
/-- A finite affine cover gives the actual Artinian global-functions comparison. -/
lemma appTop_bijective_of_cover {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hA : ∀ i, IsAffineOpen (U i)) :
    Function.Bijective f.appTop := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  apply ArtinianRelativeSectionCriterion.appTop_bijective f U hU hA s hs
  intro I hI
  exact ProperFiberTensorComplex.residue_exact f U hU hA s hs I

include s hs in
/-- Structural pullback is bijective over the original, possibly nonreduced Artinian base. -/
theorem appTop_bijective : Function.Bijective f.appTop := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hA (i : C.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (C.f i)
  exact appTop_bijective_of_cover f s hs U C.iSup_opensRange hA

/-- The actual global-functions comparison, bundled as a ring isomorphism. -/
def sectionsIso : Γ(S, ⊤) ≅ Γ(X, ⊤) :=
  (RingEquiv.ofBijective f.appTop.hom (appTop_bijective f s hs)).toCommRingCatIso

/-- The isomorphism retains the original structural pullback map. -/
lemma sectionsIso_hom : (sectionsIso f s hs).hom = f.appTop := rfl

/-- Its inverse is evaluation on the original section. -/
lemma sectionsIso_inv : (sectionsIso f s hs).inv = s.appTop := by
  apply (cancel_epi (sectionsIso f s hs).hom).mp
  rw [Iso.hom_inv_id, sectionsIso_hom, ← Scheme.Hom.comp_appTop, hs,
    Scheme.Hom.id_appTop]

end FLT.Mazur.ArtinianProperRelativeFunctions
