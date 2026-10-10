/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineProjectiveRefinement

/-!
# Gluing the projective point of a locally framed split sheaf inclusion

Local frames and local splittings on an actual affine open cover construct
a global projective morphism. Overlap compatibility is proved on common
affine refinements, including when the source line is globally nontrivial.
The ambient sheaf here is globally free.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFramedSplitLineProjective
open FCurve ProjectiveSpace AffineSplitLineCoordinates
variable {X : Scheme.{u}} {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) (C : X.OpenCover.{v})
variable [∀ i, IsAffine (C.X i)]
variable (e : ∀ i, (pullback (C.f i)).obj L ≅ structureModule (C.X i))
variable (r : ∀ i, SheafOfModules.free ι ⟶ (pullback (C.f i)).obj L)
variable (hr : ∀ i, SplitSheafLinePullback.inclusion (C.f i) s ≫ r i = 𝟙 _)

/-- The original local frame gives a point over the common global coefficient ring. -/
def localPoint (i : C.I₀) : C.X i ⟶ space Γ(X, ⊤) ι :=
  projectivePoint (e i) (SplitSheafLinePullback.inclusion (C.f i) s) (r i) (hr i) ≫
    coefficientMap (C.f i).appTop.hom ι

/-- Actual common affine refinements prove compatibility on the whole overlap. -/
lemma localPoint_compatible (i j : C.I₀) :
    Limits.pullback.fst (C.f i) (C.f j) ≫ localPoint s C e r hr i =
      Limits.pullback.snd (C.f i) (C.f j) ≫ localPoint s C e r hr j := by
  apply (Limits.pullback (C.f i) (C.f j)).affineCover.hom_ext
  intro a
  let t := (Limits.pullback (C.f i) (C.f j)).affineCover.f a
  have h : (t ≫ Limits.pullback.fst (C.f i) (C.f j)) ≫ C.f i =
      (t ≫ Limits.pullback.snd (C.f i) (C.f j)) ≫ C.f j := by
    simp only [Category.assoc, Limits.pullback.condition]
  exact (Category.assoc _ _ _).symm.trans
    ((projectivePoint_common_refinement s
      (t ≫ Limits.pullback.fst (C.f i) (C.f j))
      (t ≫ Limits.pullback.snd (C.f i) (C.f j)) (C.f i) (C.f j) h
      (e i) (e j) (r i) (r j) (hr i) (hr j)).trans (Category.assoc _ _ _))

/-- The actual locally split inclusion constructs a global projective scheme morphism. -/
def morphism : X ⟶ space Γ(X, ⊤) ι :=
  C.glueMorphisms (localPoint s C e r hr) (localPoint_compatible s C e r hr)

/-- The global construction recovers every original local frame point. -/
@[reassoc]
lemma ι_morphism (i : C.I₀) :
    C.f i ≫ morphism s C e r hr = localPoint s C e r hr i :=
  C.ι_glueMorphisms _ _ i

/-- Recovery of the original local points determines the constructed morphism uniquely. -/
lemma morphism_unique (p : X ⟶ space Γ(X, ⊤) ι)
    (hp : ∀ i, C.f i ≫ p = localPoint s C e r hr i) : p = morphism s C e r hr := by
  apply C.hom_ext
  intro i
  exact (hp i).trans (ι_morphism s C e r hr i).symm

/-- All source frames and local retractions on the cover give the same global point. -/
lemma morphism_choices (d : ∀ i, (pullback (C.f i)).obj L ≅ structureModule (C.X i))
    (q : ∀ i, SheafOfModules.free ι ⟶ (pullback (C.f i)).obj L)
    (hq : ∀ i, SplitSheafLinePullback.inclusion (C.f i) s ≫ q i = 𝟙 _) :
    morphism s C e r hr = morphism s C d q hq := by
  apply C.hom_ext
  intro i
  rw [ι_morphism, ι_morphism]
  exact congrArg (· ≫ coefficientMap (C.f i).appTop.hom ι)
    (projectivePoint_choices (d i) (e i) _ _ _ _ _)


/-- The glued morphism lies over the original scheme's canonical coefficient map. -/
lemma morphism_baseProjection :
    morphism s C e r hr ≫ baseProjection Γ(X, ⊤) ι = X.toSpecΓ := by
  apply C.hom_ext
  intro i
  rw [ι_morphism_assoc]
  unfold localPoint
  rw [Category.assoc, coefficientMap_baseProjection, ← Category.assoc,
    projectivePoint_baseProjection]
  exact (Scheme.toSpecΓ_naturality (C.f i)).symm

end FLT.Mazur.LocallyFramedSplitLineProjective
