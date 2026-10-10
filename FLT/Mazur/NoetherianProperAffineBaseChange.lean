/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianProperAffineBaseChange
public import FLT.Mazur.NoetherianStructureTensorComplex

/-!
# Arbitrary affine base change from a Noetherian base

The original structural pullback is bijective on every affine base change of
a pointed flat proper family with geometrically connected reduced fibers.
The new base may be nonflat, nonreduced, non-Noetherian, or infinite over the
original Noetherian affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FLT.Mazur.ArtinianProperAffineBaseChange
namespace FLT.Mazur.NoetherianProperAffineBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsAffine T]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]

include h s hs in
/-- Actual structural pullback is bijective after every affine change of base. -/
theorem appTop_bijective : Function.Bijective q.appTop := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hA (i : C.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (C.f i)
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have he := NoetherianStructureTensorComplex.cover_exact f s hs U C.iSup_opensRange hA Γ(T, ⊤)
  have hsurj := CartesianStructureComplexGluing.appTop_surjective_of_exact h U
    C.iSup_opensRange hA (fun i j ↦ (hA i).inf (hA j)) he
  have hleft : Function.LeftInverse (sectionOfSquare h s hs).appTop q.appTop :=
    SchemeRelativeNilpotentSections.evaluation_pullback q (sectionOfSquare h s hs)
      (sectionOfSquare_projection h s hs)
  exact ⟨hleft.injective, hsurj⟩

/-- The base-change comparison retains the actual projection on global functions. -/
def sectionsIso : Γ(T, ⊤) ≅ Γ(P, ⊤) :=
  (RingEquiv.ofBijective q.appTop.hom (appTop_bijective h s hs)).toCommRingCatIso

/-- The forward isomorphism is structural pullback. -/
lemma sectionsIso_hom : (sectionsIso h s hs).hom = q.appTop := rfl

/-- The inverse is evaluation along the constructed cartesian section. -/
lemma sectionsIso_inv : (sectionsIso h s hs).inv = (sectionOfSquare h s hs).appTop := by
  apply (cancel_epi (sectionsIso h s hs).hom).mp
  rw [Iso.hom_inv_id, sectionsIso_hom, ← Scheme.Hom.comp_appTop,
    sectionOfSquare_projection, Scheme.Hom.id_appTop]

end FLT.Mazur.NoetherianProperAffineBaseChange
