/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineProjectiveFrame
public import FLT.Mazur.AffineSectionLineCoefficientMap

/-!
# Geometric pullback of the global projective morphism of a split vector

Compare the actual points on inverse images of coordinate principal opens.
The comparison glues to the entire original affine source, with no chosen
globally invertible coordinate and no supplied point-compatibility hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLinePrincipalPoints
open ProjectiveSpace
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {ι : Type u} (v : ι → Γ(Y, ⊤))

/-- The local image points commute with the genuine restriction of a scheme morphism. -/
lemma point_pullback (i : ι) (U : Y.Opens) (V : X.Opens)
    [IsAffine U.toScheme] [IsAffine V.toScheme] (h : V ≤ f ⁻¹ᵁ U)
    (hi : U ≤ Y.basicOpen (v i)) (hj : V ≤ X.basicOpen (f.appTop (v i))) :
    f.resLE U V h ≫ point v i U hi =
      point (fun j ↦ f.appTop (v j)) i V hj ≫ coefficientMap f.appTop.hom ι := by
  rw [point, affineGeneratorPoint_pullback, point, affineGeneratorPoint_coefficientMap]
  have hc : (f.resLE U V h).appTop.hom.comp U.ι.appTop.hom =
      V.ι.appTop.hom.comp f.appTop.hom := by
    change (f.resLE U V h ≫ U.ι).appTop.hom = (V.ι ≫ f).appTop.hom
    rw [Scheme.Hom.resLE_comp_ι]
  have hv : (fun j ↦ (f.resLE U V h).appTop (U.ι.appTop (v j))) =
      (fun j ↦ V.ι.appTop (f.appTop (v j))) :=
    funext fun j ↦ DFunLike.congr_fun hc (v j)
  simp only [hc, hv, affineGeneratorPoint]
  apply (affineSectionLinePoint_eq_iff _ i i _ _).mpr
  rfl

variable [Finite ι]

/-- The glued projective morphism commutes with arbitrary affine geometric pullback. -/
lemma morphism_pullback (r : (ι → Γ(Y, ⊤)) →ₗ[Γ(Y, ⊤)] Γ(Y, ⊤)) (hr : r v = 1)
    (q : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤))
    (hq : q (fun j ↦ f.appTop (v j)) = 1) :
    f ≫ morphism v r hr =
      morphism (fun j ↦ f.appTop (v j)) q hq ≫ coefficientMap f.appTop.hom ι := by
  apply (openCover (fun j ↦ f.appTop (v j)) q hq).hom_ext
  intro i
  change ι at i
  change (X.basicOpen (f.appTop (v i))).ι ≫ (f ≫ morphism v r hr) =
    (X.basicOpen (f.appTop (v i))).ι ≫
      (morphism (fun j ↦ f.appTop (v j)) q hq ≫ coefficientMap f.appTop.hom ι)
  have h : X.basicOpen (f.appTop (v i)) ≤ f ⁻¹ᵁ Y.basicOpen (v i) := by
    rw [Scheme.Hom.preimage_basicOpen_top]
  calc
    _ = f.resLE _ _ h ≫ ((Y.basicOpen (v i)).ι ≫ morphism v r hr) := by
      simp only [← Category.assoc, Scheme.Hom.resLE_comp_ι]
    _ = f.resLE _ _ h ≫ point v i (Y.basicOpen (v i)) le_rfl := by rw [ι_morphism]
    _ = point (fun j ↦ f.appTop (v j)) i (X.basicOpen (f.appTop (v i))) le_rfl ≫
        coefficientMap f.appTop.hom ι := point_pullback f v i _ _ h le_rfl le_rfl
    _ = _ := (ι_morphism_assoc (fun j ↦ f.appTop (v j)) q hq i _).symm

end FLT.Mazur.SplitLinePrincipalPoints
