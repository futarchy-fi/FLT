/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormCartesianCharts

/-!
# Base change of norms glued from local finite bases

The entire original free cover pulls back to a genuine free cover. Its local
cartesian norm equations glue, and cover independence permits any unrelated
free cover on the changed target.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineNormCartesianGluing
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T Y : Scheme.{u}} [IsAffine T] [IsAffine Y]
  {a : P ⟶ X} {b : P ⟶ T} {f : X ⟶ Y} {g : T ⟶ Y}
  (H : IsPullback a b f g) [IsAffineHom f] [IsAffineHom b]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The changed charts are whole target preimages of the original charts. -/
def changedChart (i : ι) : T.affineOpens := ⟨g ⁻¹ᵁ (U i).1, (U i).2.preimage g⟩

omit [IsAffineHom b] in
include H hU in
/-- The original finite bases construct finite bases on the entire changed preimages. -/
theorem changedChart_basis (i : ι) :
    AffineOpenNorm.HasBasis b (changedChart (g := g) U i) :=
  AffineNormCartesianCharts.hasBasis H (U i) (changedChart U i) le_rfl (hU i)

include hcover in
/-- The changed charts still cover the entire target. -/
theorem changedChart_cover : ⨆ i, (changedChart (g := g) U i).1 = ⊤ :=
  g.iSup_preimage_eq_top hcover

/-- The norm constructed on the pulled-back charts is the pullback of the original norm. -/
theorem norm_pullback (s : Γ(X, ⊤)) :
    AffineNormGluing.norm b (changedChart (g := g) U) (changedChart_basis H U hU)
      (changedChart_cover U hcover) (a.appTop s) =
        g.appTop (AffineNormGluing.norm f U hU hcover s) := by
  symm
  apply AffineNormGluing.eq_norm
  intro i
  rw [AffineNormCartesianCharts.chart_pullback H (U i) (changedChart U i) le_rfl (hU i)]
  dsimp only [changedChart]
  rw [Scheme.Hom.appLE_eq_app]
  have hn := congrArg (g.app (U i).1) (AffineNormGluing.norm_chart f U hU hcover s i)
  exact (ConcreteCategory.congr_hom (g.naturality (homOfLE le_top).op)
    (AffineNormGluing.norm f U hU hcover s)).symm.trans hn

include H in
/-- Independent free covers on the changed target compute the same cartesian norm. -/
theorem norm_pullback_any {κ : Type w} (V : κ → T.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis b (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) :
    AffineNormGluing.norm b V hV hcoverV (a.appTop s) =
      g.appTop (AffineNormGluing.norm f U hU hcover s) := by
  rw [AffineNormGluing.norm_independent b V hV hcoverV (changedChart U)
    (changedChart_basis H U hU) (changedChart_cover U hcover)]
  exact norm_pullback H U hU hcover s

end FLT.Mazur.AffineNormCartesianGluing
