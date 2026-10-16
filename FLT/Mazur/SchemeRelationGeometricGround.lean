/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFunctionGroundChange
public import FLT.Mazur.AlgebraEqualizerCoordinates

/-!
# Full relation invariants after geometric flat ground change

For quasi-compact separated source and relation schemes, flat affine ground
change identifies the full tensor endpoint equations with the actual geometric
endpoint equations. Both projections are retained, as is the source inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeRelationGeometricGround
open SchemeFunctionGroundChange FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme.{0}} (g : T ⟶ S)
  {A D : Over S} {A' D' : Over T}
  {i : A'.left ⟶ A.left} {z : D'.left ⟶ D.left}
  (hA : IsPullback i A'.hom A.hom g) (hD : IsPullback z D'.hom D.hom g)
  (p q : D ⟶ A) (p' q' : D' ⟶ A')
  (hp : z ≫ p.left = p'.left ≫ i) (hq : z ≫ q.left = q'.left ≫ i)

attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

variable [CompactSpace A.left] [A.left.IsSeparated]
  [CompactSpace D.left] [D.left.IsSeparated] [IsAffine T] [IsAffine S] [Flat g]

include hp in
/-- Each tensor endpoint becomes its actual geometric base-changed endpoint. -/
theorem endpoint_square :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    (sectionMap p').comp (sectionsEquiv g hA).toAlgHom =
      (sectionsEquiv g hD).toAlgHom.comp (tensorMap Γ(T, ⊤) (sectionMap p)) := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  ext x
  exact (comparison_natural g hD hA p p' hp.symm x).symm

/-- Full tensor equations are exactly the full geometric endpoint equations. -/
def tensorEquiv :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    AlgHom.equalizer (tensorMap Γ(T, ⊤) (sectionMap p))
      (tensorMap Γ(T, ⊤) (sectionMap q)) ≃ₐ[Γ(T, ⊤)]
        AlgHom.equalizer (sectionMap p') (sectionMap q') := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  exact AlgebraEqualizerCoordinates.equiv _ _ _ _ (sectionsEquiv g hA) (sectionsEquiv g hD)
    (endpoint_square g hA hD p p' hp) (endpoint_square g hA hD q q' hq)

/-- The full geometric comparison retains every source coefficient. -/
theorem tensorEquiv_val :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∀ a : AlgHom.equalizer (tensorMap Γ(T, ⊤) (sectionMap p))
      (tensorMap Γ(T, ⊤) (sectionMap q)),
      (tensorEquiv g hA hD p q p' q' hp hq a).val = sectionsEquiv g hA a.val := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  exact fun _ ↦ rfl

/-- Original invariant functions commute with actual geometric flat affine ground change. -/
def invariantsEquiv :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] AlgHom.equalizer (sectionMap p) (sectionMap q) ≃ₐ[Γ(T, ⊤)]
      AlgHom.equalizer (sectionMap p') (sectionMap q') := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  let _ : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := g.flat_appTop
  exact (FlatAlgebraEqualizer.comparison (sectionMap p) (sectionMap q) Γ(T, ⊤)).trans
    (tensorEquiv g hA hD p q p' q' hp hq)

/-- The geometric invariant comparison is scalar multiplication of the original pullback. -/
theorem invariantsEquiv_tmul (b : Γ(T, ⊤))
    (a : AlgHom.equalizer (sectionMap p) (sectionMap q)) :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    (invariantsEquiv g hA hD p q p' q' hp hq (b ⊗ₜ[Γ(S, ⊤)] a)).val =
      A'.hom.appTop b * i.appTop a.val := rfl

end FLT.Mazur.SchemeRelationGeometricGround
