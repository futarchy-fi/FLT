/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeTranslationNormNaturality
public import FLT.Mazur.AffineProductNormFiber
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Full-fiber support of the glued regular norm

Affine tests compute the determinant. Cartesian lifting of points identifies
its support on the entire original product, even when the source is nonaffine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation AffineProductTranslationNorm
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (Y V : Over (Spec (.of R))) [IsAffine V.left]
/-- The original translation structural algebra. -/
local instance fiberTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((prod Y V).left, ⊤))
local notation "π" => Over.Hom.left (prod.fst : prod Y V ⟶ Y)

/-- Every affine test detects nonvanishing using its full independent product fiber. -/
theorem mem_basicOpen_regularNorm_test {T : Over (Spec (.of R))} [IsAffine T.left]
    (t : T ⟶ Y) (x : T.left) :
    t.left x ∈ Y.left.basicOpen (regularNorm Y V b s) ↔
      ∀ z : (prod T V).left, (prod.fst : prod T V ⟶ T).left z = x →
        (prod.map t (𝟙 V)).left z ∈ (prod Y V).left.basicOpen s := by
  change x ∈ t.left ⁻¹ᵁ Y.left.basicOpen (regularNorm Y V b s) ↔ _
  rw [Scheme.preimage_basicOpen_top, regularNorm, norm_test]
  dsimp only [localNorm]
  rw [mem_basicOpen_envelopeNorm_iff]
  simp only [← Scheme.preimage_basicOpen_top]
  rfl

/-- Nonvanishing of the glued norm is equivalent to nonvanishing on the whole original fiber. -/
theorem mem_basicOpen_regularNorm_iff (y : Y.left) :
    y ∈ Y.left.basicOpen (regularNorm Y V b s) ↔
      ∀ z : (prod Y V).left, (π) z = y → z ∈ (prod Y V).left.basicOpen s := by
  obtain ⟨i, x, hx⟩ := Y.left.affineCover.exists_eq y
  let T := coverObject Y Y.left.affineCover i
  let t : T ⟶ Y := coverArrow Y Y.left.affineCover i
  change t.left x = y at hx
  rw [← hx, mem_basicOpen_regularNorm_test Y V b s t x]
  have H := (IsPullback.of_prod_fst_with_id t V).map (Over.forget _)
  constructor
  · intro h z hz
    obtain ⟨w, hw, hwx⟩ := Scheme.exists_preimage_of_isPullback H.flip z x hz
    rw [← hw]
    exact h w hwx
  · intro h z hz
    apply h
    have he := congrArg (fun g : prod T V ⟶ Y ↦ g.left z) (prod.map_fst t (𝟙 V))
    change (π) ((prod.map t (𝟙 V)).left z) =
      t.left ((prod.fst : prod T V ⟶ T).left z) at he
    exact he.trans (congrArg t.left hz)

end FLT.Mazur.SchemeTranslationNorm
