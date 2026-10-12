/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricPullbackPointwiseEquality
public import FLT.Mazur.ProperPointwiseSectionRigidity
public import FLT.Mazur.ProperSmoothGroupGeometricHom
public import FLT.Mazur.SmoothCurveSquareGeometricIntegral

/-!
# Pointed maps preserve the original relative group laws

Geometric rigidity makes the multiplication discrepancy fiberwise trivial.
The proper global-functions comparison then kills that discrepancy over the
original locally Noetherian base, including its nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [IsLocallyNoetherian S]
  (G Z : Over S) [GrpObj G] [GrpObj Z]
  [IsProper G.hom] [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
  (f : G ⟶ Z) (hf : η[G] ≫ f = η[Z])

include hf

/-- A pointed morphism from a proper smooth relative curve preserves both original group laws. -/
theorem properRelative_isMonHom_of_one : IsMonHom f := by
  let _ : Smooth G.hom := SmoothOfRelativeDimension.smooth 1 G.hom
  let _ : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  let _ : Smooth (G ⊗ G).hom := by dsimp; infer_instance
  let _ := smoothCurveSquare_geometricallyIntegral G
  let _ : GeometricallyConnected (G ⊗ G).hom := ⟨by
    intro K _ g P p q H
    let _ := GeometricallyIntegral.geometrically_isIntegral
      (f := (G ⊗ G).hom) g p q H
    infer_instance⟩
  let d : G ⊗ G ⟶ Z := (μ[G] ≫ f) / ((f ⊗ₘ f) ≫ μ[Z])
  let t : 𝟙_ (Over S) ⟶ G ⊗ G := lift η[G] η[G]
  have ht : t ≫ d = 1 := by
    simp only [d, GrpObj.comp_div, ← Category.assoc]
    have hmul : t ≫ μ[G] = η[G] := by
      change (η[G] * η[G]) = η[G]
      simp only [MonObj.one_eq_one, _root_.one_mul]
    have hten : t ≫ (f ⊗ₘ f) = lift η[Z] η[Z] := by
      ext <;> simp [t, hf]
    rw [hmul, hf, hten]
    change η[Z] / (η[Z] * η[Z]) = 1
    simp only [MonObj.one_eq_one, _root_.one_mul, div_self']
  have hg (K : Type) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S) :
      (Over.pullback g).map d = (Over.pullback g).map (1 : G ⊗ G ⟶ Z) := by
    let F := Over.pullback g
    let _ : GrpObj (F.obj Z) := Functor.grpObjObj
    let _ : Group (F.obj (G ⊗ G) ⟶ F.obj Z) := CategoryTheory.Hom.group
    have he : F.map d * F.map ((f ⊗ₘ f) ≫ μ[Z]) =
        F.map ((f ⊗ₘ f) ≫ μ[Z]) := by
      rw [← Functor.map_mul]
      change F.map (((μ[G] ≫ f) / ((f ⊗ₘ f) ≫ μ[Z])) * ((f ⊗ₘ f) ≫ μ[Z])) = _
      rw [div_mul_cancel, properSmoothGroup_geometric_mul G Z f hf g]
    rw [Functor.map_one]
    exact mul_right_cancel (he.trans (_root_.one_mul _).symm)
  have hp (x : (G ⊗ G).left) : d.left x = d.left (t.left ((G ⊗ G).hom x)) := by
    have hd := pointwise_eq_of_geometric_pullback d 1 hg x
    have he := congrArg (fun k : 𝟙_ (Over S) ⟶ Z ↦ k.left ((G ⊗ G).hom x)) ht
    exact hd.trans he.symm
  have hd : d = 1 := by
    apply Over.OverMorphism.ext
    rw [proper_eq_section_of_pointwise (G ⊗ G).hom t.left t.w d.left hp]
    exact congrArg (fun k : 𝟙_ (Over S) ⟶ Z ↦ (G ⊗ G).hom ≫ k.left) ht
  exact ⟨hf, div_eq_one.mp hd⟩

end FLT.Mazur.FCurve
