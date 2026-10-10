/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineCoordinateNaturality
public import FLT.Mazur.SectionLinePointBaseChange

/-!
# Section-line points on the original affine test scheme

The canonical spectrum isomorphism transports section-line points back to
an arbitrary affine scheme. The construction respects geometric pullback
and detects equality of the original section submodules across charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
open NormalizedSectionLine
variable {R : Type u} [CommRing R] {ι : Type u}
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- The projective point on the original affine scheme, rather than only its spectrum. -/
def affineSectionLinePoint (φ : R →+* Γ(X, ⊤)) (i : ι) (L : Chart Γ(X, ⊤) ι i) :
    X ⟶ space R ι := X.isoSpec.hom ≫ sectionLinePoint R ι φ i L

/-- Equality of actual affine points is equality of their original section submodules. -/
lemma affineSectionLinePoint_eq_iff (φ : R →+* Γ(X, ⊤)) (i j : ι)
    (L : Chart Γ(X, ⊤) ι i) (N : Chart Γ(X, ⊤) ι j) :
    affineSectionLinePoint φ i L = affineSectionLinePoint φ j N ↔ L.val = N.val := by
  rw [affineSectionLinePoint, affineSectionLinePoint, cancel_epi,
    sectionLinePoint_eq_iff]

/-- Geometric pullback extends the actual coordinate submodule. -/
lemma affineSectionLinePoint_pullback (f : X ⟶ Y) (φ : R →+* Γ(Y, ⊤)) (i : ι)
    (L : Chart Γ(Y, ⊤) ι i) :
    f ≫ affineSectionLinePoint φ i L =
      affineSectionLinePoint (f.appTop.hom.comp φ) i (baseChange f.appTop.hom i L) := by
  rw [affineSectionLinePoint, ← Category.assoc, ← Scheme.isoSpec_hom_naturality,
    Category.assoc]
  exact congrArg (X.isoSpec.hom ≫ ·) (sectionLinePoint_map R ι f.appTop.hom φ i L)

/-- The affine point of a unit-normalized vector uses its actual image line. -/
def affineGeneratorPoint (φ : R →+* Γ(X, ⊤)) (v : ι → Γ(X, ⊤))
    (i : ι) (a : Γ(X, ⊤)ˣ) (hi : v i = a) : X ⟶ space R ι :=
  affineSectionLinePoint φ i (unitCoordinateLine v i a hi)

/-- Any two invertible coordinates of the same vector give the same affine point. -/
lemma affineGeneratorPoint_eq (φ : R →+* Γ(X, ⊤)) (v : ι → Γ(X, ⊤))
    (i j : ι) (a b : Γ(X, ⊤)ˣ) (hi : v i = a) (hj : v j = b) :
    affineGeneratorPoint φ v i a hi = affineGeneratorPoint φ v j b hj :=
  (affineSectionLinePoint_eq_iff φ i j _ _).mpr rfl

/-- The vector construction commutes with the original affine structural map. -/
lemma affineGeneratorPoint_pullback (f : X ⟶ Y) (φ : R →+* Γ(Y, ⊤))
    (v : ι → Γ(Y, ⊤)) (i : ι) (a : Γ(Y, ⊤)ˣ) (hi : v i = a) :
    f ≫ affineGeneratorPoint φ v i a hi =
      affineGeneratorPoint (f.appTop.hom.comp φ) (fun j ↦ f.appTop (v j)) i
        (Units.map f.appTop.hom.toMonoidHom a) (congrArg f.appTop hi) := by
  rw [affineGeneratorPoint, affineSectionLinePoint_pullback, baseChange_unitCoordinateLine]
  rfl

end FLT.Mazur.ProjectiveSpace
