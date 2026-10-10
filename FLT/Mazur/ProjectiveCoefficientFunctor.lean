/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceAffineBase

/-!
# Functorial projective coefficient charts

Coefficient scheme maps preserve identity and composition. In particular,
the maps attached to affine open inclusions form coherent refinement paths.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The identity coefficient map is the graded identity. -/
lemma coefficientGradedMap_id (ι : Type u) :
    coefficientGradedMap (RingHom.id R) ι = .id (grading R ι) := by
  ext p : 1
  exact MvPolynomial.map_id p

/-- Composition of coefficient homomorphisms is composition of graded maps. -/
lemma coefficientGradedMap_comp (φ : R →+* S) (ψ : S →+* T) (ι : Type u) :
    coefficientGradedMap (ψ.comp φ) ι =
      (coefficientGradedMap ψ ι).comp (coefficientGradedMap φ ι) := by
  ext p : 1
  exact (MvPolynomial.map_map φ ψ p).symm

/-- Identity coefficient change induces the identity projective scheme morphism. -/
lemma coefficientMap_id (ι : Type u) : coefficientMap (RingHom.id R) ι = 𝟙 _ := by
  change Proj.map _ _ = _
  simpa only [coefficientGradedMap_id] using Proj.map_id (𝒜 := grading R ι)

/-- Successive coefficient changes agree with their composite. -/
lemma coefficientMap_comp (φ : R →+* S) (ψ : S →+* T) (ι : Type u) :
    coefficientMap ψ ι ≫ coefficientMap φ ι = coefficientMap (ψ.comp φ) ι := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  congr 1
  exact (coefficientGradedMap_comp φ ψ ι).symm

/-- The projective coefficient map for the identity affine morphism is identity. -/
lemma coefficientMap_appTop_id (X : Scheme.{u}) (ι : Type u) :
    coefficientMap (Scheme.Hom.appTop (𝟙 X)).hom ι = 𝟙 _ := by
  have h : (Scheme.Hom.appTop (𝟙 X)).hom = RingHom.id Γ(X, ⊤) := by ext r; rfl
  rw [h, coefficientMap_id]

/-- Projective coefficient charts respect composition of actual scheme morphisms. -/
lemma coefficientMap_appTop_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (ι : Type u) :
    coefficientMap f.appTop.hom ι ≫ coefficientMap g.appTop.hom ι =
      coefficientMap (f ≫ g).appTop.hom ι := by
  rw [coefficientMap_comp]
  congr 1

/-- Projective charts have a single coefficient map along nested open refinements. -/
lemma coefficientMap_homOfLE_comp {X : Scheme.{u}} {U V W : X.Opens}
    (h : V ≤ U) (k : W ≤ V) (ι : Type u) :
    coefficientMap (X.homOfLE k).appTop.hom ι ≫
      coefficientMap (X.homOfLE h).appTop.hom ι =
        coefficientMap (X.homOfLE (k.trans h)).appTop.hom ι := by
  rw [coefficientMap_appTop_comp]
  have hcomp : X.homOfLE k ≫ X.homOfLE h = X.homOfLE (k.trans h) := by
    apply (cancel_mono U.ι).mp
    simp
  rw [hcomp]

end FLT.Mazur.ProjectiveSpace
