/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineProjectiveMorphism

/-!
# Frame independence of the constructed global projective point

The global morphism restricts to the prescribed point on every affine
subopen where a coordinate is invertible. It is independent of the chosen
retraction and of multiplication of the original generator by a unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLinePrincipalPoints
open NormalizedSectionLine ProjectiveSpace
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u}
variable (v : ι → Γ(X, ⊤))

omit [IsAffine X] in
/-- Unit rescaling preserves each actual coordinate principal open. -/
lemma basicOpen_unit_smul (c : Γ(X, ⊤)ˣ) (i : ι) :
    X.basicOpen (((c : Γ(X, ⊤)) • v) i) = X.basicOpen (v i) := by
  change X.basicOpen ((c : Γ(X, ⊤)) * v i) = _
  rw [X.basicOpen_mul, X.basicOpen_of_isUnit c.isUnit, top_inf_eq]

/-- A unit change of source frame preserves the actual local image point. -/
lemma point_unit_smul (c : Γ(X, ⊤)ˣ) (i j : ι) (U : X.Opens) [IsAffine U.toScheme]
    (hi : U ≤ X.basicOpen (((c : Γ(X, ⊤)) • v) i)) (hj : U ≤ X.basicOpen (v j)) :
    point ((c : Γ(X, ⊤)) • v) i U hi = point v j U hj := by
  unfold point affineGeneratorPoint
  apply (affineSectionLinePoint_eq_iff _ i j _ _).mpr
  change LinearMap.range (LinearMap.toSpanSingleton Γ(U.toScheme, ⊤)
    (ι → Γ(U.toScheme, ⊤)) (fun k ↦ U.ι.appTop ((c : Γ(X, ⊤)) * v k))) = _
  have hv : (fun k ↦ U.ι.appTop ((c : Γ(X, ⊤)) * v k)) =
      (Units.map U.ι.appTop.hom.toMonoidHom c : Γ(U.toScheme, ⊤)) •
        (fun k ↦ U.ι.appTop (v k)) := by
    ext k
    exact map_mul U.ι.appTop.hom _ _
  rw [hv]
  exact generatorRange_unit_smul _ _

variable [Finite ι] (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hr : r v = 1)

/-- Every affine subopen with an invertible coordinate recovers its actual normalized point. -/
lemma morphism_onOpen (i : ι) (U : X.Opens) [IsAffine U.toScheme]
    (hi : U ≤ X.basicOpen (v i)) :
    U.ι ≫ morphism v r hr = point v i U hi := by
  rw [← X.homOfLE_ι hi, Category.assoc, ι_morphism, point_restrict]

/-- The actual projective morphism is independent of the retraction certifying its cover. -/
lemma morphism_retraction_eq (s : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hs : s v = 1) :
    morphism v r hr = morphism v s hs := by
  apply morphism_unique v s hs
  exact ι_morphism v r hr

/-- A unit frame change leaves the constructed global projective morphism unchanged. -/
lemma morphism_unit_smul (c : Γ(X, ⊤)ˣ)
    (s : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hs : s ((c : Γ(X, ⊤)) • v) = 1) :
    morphism ((c : Γ(X, ⊤)) • v) s hs = morphism v r hr := by
  apply morphism_unique v r hr
  intro i
  have hi : X.basicOpen (v i) ≤ X.basicOpen (((c : Γ(X, ⊤)) • v) i) :=
    (basicOpen_unit_smul v c i).ge
  rw [morphism_onOpen _ s hs i _ hi]
  exact point_unit_smul v c i i _ hi le_rfl

omit [IsAffine X] [Finite ι] in
include hr in
/-- A unit change of generator has a constructed retraction, rather than extra splitting data. -/
lemma unit_smul_retraction (c : Γ(X, ⊤)ˣ) :
    ((↑c⁻¹ : Γ(X, ⊤)) • r) ((c : Γ(X, ⊤)) • v) = 1 := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hr, mul_one, Units.mul_inv]

end FLT.Mazur.SplitLinePrincipalPoints
