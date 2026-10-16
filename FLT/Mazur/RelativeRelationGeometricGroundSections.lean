/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationGeometricGround
public import FLT.Mazur.RelativeRelationInvariantSectionRings

/-!
# Geometric ground comparison with the actual invariant sheaf

The full geometric endpoint equalizer is the ring of global sections of the
original invariant sheaf. Combining this with flat ground comparison identifies
full tensor equations with actual invariant sheaf sections upstairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeFunctionGroundChange SchemeRelationGeometricGround
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} {A D : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

/-- Whole invariant-sheaf sections in structural global-function coordinates. -/
def topFunctionEquiv : (invariantSheaf e).obj.obj (op ⊤) ≃+*
    AlgHom.equalizer (sectionMap p) (sectionMap q) := by
  let E := invariantSectionRingEquiv e ⊤
  have h : originalInvariantSections (p := p) (q := q) (pullOpen e ⊤).val
      (pullOpen_preimage_eq e ⊤) =
        (AlgHom.equalizer (sectionMap p) (sectionMap q)).toSubring := by
    ext a
    change Γ(A.left, ⊤) at a
    change p.left.appTop a = q.left.appLE ⊤ ⊤ _ a ↔
      p.left.appTop a = q.left.appTop a
    simp [Scheme.Hom.appLE]
  exact E.trans (RingEquiv.subringCongr h)

/-- The structural coordinates retain the actual invariant-sheaf inclusion. -/
theorem topFunctionEquiv_val (a : (invariantSheaf e).obj.obj (op ⊤)) :
    (topFunctionEquiv e a).val = (invariantInclusion e).hom.app (op ⊤) a := rfl

variable {T : Scheme.{0}} (g : T ⟶ S) {A' D' : Over T}
  {i : A'.left ⟶ A.left} {z : D'.left ⟶ D.left}
  (hA : IsPullback i A'.hom A.hom g) (hD : IsPullback z D'.hom D.hom g)
  {p' q' : D' ⟶ A'} (e' : CategoryTheory.EquivalenceRelation p' q')
  (hp : z ≫ p.left = p'.left ≫ i) (hq : z ≫ q.left = q'.left ≫ i)
  [CompactSpace A.left] [A.left.IsSeparated]
  [CompactSpace D.left] [D.left.IsSeparated] [IsAffine T] [IsAffine S] [Flat g]

/-- Full tensor endpoint equations identify with actual invariant-sheaf sections upstairs. -/
def tensorInvariantSheafEquiv :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap p))
      (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap q)) ≃+*
        (invariantSheaf e').obj.obj (op ⊤) := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  exact (tensorEquiv g hA hD p q p' q' hp hq).toRingEquiv.trans (topFunctionEquiv e').symm

/-- The sheaf comparison keeps the actual function on the geometric source. -/
theorem tensorInvariantSheafEquiv_val :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∀ a : AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap p))
      (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap q)),
      (invariantInclusion e').hom.app (op ⊤)
        (tensorInvariantSheafEquiv g hA hD e' hp hq a) = sectionsEquiv g hA a.val := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  dsimp only
  intro a
  have h := congrArg Subtype.val ((topFunctionEquiv e').apply_symm_apply
    (tensorEquiv g hA hD p q p' q' hp hq a))
  exact h

end FLT.Mazur.RelativeRelationOrbit
