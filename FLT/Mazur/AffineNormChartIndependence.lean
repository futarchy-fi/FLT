/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormGluing

/-!
# Independence of the affine norm cover

The glued norm agrees with every genuine free chart, not just the charts
chosen to define it. Two unrelated covers therefore give the same section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineNormGluing
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The global norm recovers the determinant on any additional free affine chart. -/
theorem norm_any_chart (V : Y.affineOpens) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE le_top).op (norm f U hU hcover s) = chart f V s := by
  apply Y.sheaf.eq_of_locally_eq' (fun i ↦ V.1 ⊓ (U i).1) V.1
    (fun _ ↦ homOfLE inf_le_left) (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  let W : Y.affineOpens := ⟨V.1 ⊓ (U i).1, V.2.inf (U i).2⟩
  have hWV : W ≤ V := show V.1 ⊓ (U i).1 ≤ V.1 from inf_le_left
  have hWU : W ≤ U i := show V.1 ⊓ (U i).1 ≤ (U i).1 from inf_le_right
  change Y.presheaf.map (homOfLE hWV).op
    (Y.presheaf.map (homOfLE le_top).op (norm f U hU hcover s)) =
      Y.presheaf.map (homOfLE hWV).op (chart f V s)
  rw [chart_restrict f hV hWV]
  have hi := congrArg (Y.presheaf.map (homOfLE hWU).op)
    (norm_chart f U hU hcover s i)
  rw [chart_restrict f (hU i) hWU] at hi
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] at hi ⊢
  convert hi using 2

/-- Changing all local bases and the entire cover leaves the original global norm unchanged. -/
theorem norm_independent {κ : Type w} (V : κ → Y.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis f (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) : norm f U hU hcover s = norm f V hV hcoverV s := by
  apply eq_norm
  intro j
  exact norm_any_chart f U hU hcover (V j) (hV j) s

/-- The norm construction is a multiplicative map on the original global sections. -/
def normHom : Γ(X, ⊤) →* Γ(Y, ⊤) where
  toFun := norm f U hU hcover
  map_one' := norm_one f U hU hcover
  map_mul' := norm_mul f U hU hcover

end FLT.Mazur.AffineNormGluing
