/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicAffineGeometry
public import FLT.Mazur.PolygonCyclicDivisorPullback

/-!
# Constant cyclic groups over arbitrary bases

The coproduct of n copies of any base scheme is finite etale of degree n.
The degree proof descends from the integer model by the actual coproduct
base-change isomorphism, so it also covers nonaffine and empty schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.ConstantCyclicRelativeGeometry

variable (S : Scheme.{0}) (n : ℕ) [NeZero n]

/-- The underlying scheme is the actual coproduct of copies of the base. -/
def underlyingIso : (∐ fun _ : ZMod n ↦ S) ≅ (ConstantCyclicGroup.model S n).left :=
  asIso (sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)))

/-- Each underlying component retains its label. -/
@[reassoc] theorem component_underlyingIso (i : ZMod n) :
    Sigma.ι _ i ≫ (underlyingIso S n).hom =
      (ConstantCyclicGroup.component S n i).left :=
  ι_comp_sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)) i

/-- The constant cyclic group has rank n over every scheme. -/
theorem degree : FCurve.FiniteLocallyFreeDegree (ConstantCyclicGroup.model S n).hom n := by
  let g : S ⟶ Spec (.of ℤ) := specZIsTerminal.from S
  exact (FCurve.finiteLocallyFreeDegree_iff_of_overIso
    (ConstantCyclicPullback.equivalence g n)).mpr
      ((ConstantCyclicAffineGeometry.degree ℤ n).baseChange g)

/-- The constant cyclic group is etale over an arbitrary base. -/
theorem etale : Etale (ConstantCyclicGroup.model S n).hom := by
  have he : (underlyingIso S n).hom ≫ (ConstantCyclicGroup.model S n).hom =
      Sigma.desc (fun _ : ZMod n ↦ 𝟙 S) := by
    apply Sigma.hom_ext
    intro i
    rw [component_underlyingIso_assoc, Sigma.ι_comp_desc]
    exact (ConstantCyclicGroup.component S n i).w
  have : Etale ((underlyingIso S n).hom ≫ (ConstantCyclicGroup.model S n).hom) := by
    rw [he]
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (@Etale)
    (underlyingIso S n).hom (ConstantCyclicGroup.model S n).hom).mp inferInstance

/-- Every morphism from the constant scheme is its coproduct of sections. -/
@[reassoc] theorem underlying_components {X : Over S}
    (d : ConstantCyclicGroup.model S n ⟶ X) :
    (underlyingIso S n).hom ≫ d.left = Sigma.desc (fun i : ZMod n ↦
      (ConstantCyclicGroup.component S n i ≫ d).left) := by
  apply Sigma.hom_ext
  intro i
  rw [component_underlyingIso_assoc, Sigma.ι_comp_desc]
  rfl

end FLT.Mazur.ConstantCyclicRelativeGeometry
