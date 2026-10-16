/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledQuotientDescent

/-!
# Gluing the complete original arithmetic diagram

Natural compatible maps on every full labeled chart glue to a natural map
from the original global quotient system. All orders and chart restrictions
are retained, and the assembled map is uniquely determined by those data.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hk : k ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H
local notation "U" => arithmeticLabeledOpenCover hπ data H
local notation "X" => finiteGlobalArithmeticSystem hπ data k hk
variable {Y : ℕ ⥤ Scheme}
  (f : ∀ i, arithmeticLabeledChartSystem hπ data H k hk i ⟶ Y)
  (hf : ∀ (m : ℕ) (i j : ArithmeticChartLabel k),
    pullback.fst (arithmeticLabeledAtlasMap hπ data H m k hk i)
      (arithmeticLabeledAtlasMap hπ data H m k hk j) ≫ (f i).app m =
    pullback.snd (arithmeticLabeledAtlasMap hπ data H m k hk i)
      (arithmeticLabeledAtlasMap hπ data H m k hk j) ≫ (f j).app m)

/-- Compatible natural full chart maps glue over the entire original quotient system. -/
def arithmeticLabeledSystemDesc : X ⟶ Y :=
  NatTrans.ofSequence (fun m => (U m k hk).glueMorphisms (fun i => (f i).app m) (hf m)) (by
    intro m
    simp only [finiteGlobalArithmeticSystem, Functor.ofSequence_map_homOfLE_succ]
    apply (arithmeticLabeledQuotient_square_iff hπ data H m k hk _ _ _).mpr
    intro i
    have h₀ : c m k hk i ≫ (U m k hk).glueMorphisms (fun i => (f i).app m) (hf m) =
        (f i).app m := (U m k hk).ι_glueMorphisms _ _ i
    have h₁ : c (m + 1) k hk i ≫
        (U (m + 1) k hk).glueMorphisms (fun i => (f i).app (m + 1)) (hf (m + 1)) =
          (f i).app (m + 1) := (U (m + 1) k hk).ι_glueMorphisms _ _ i
    rw [h₁, ← Category.assoc, h₀]
    simpa only [arithmeticLabeledChartSystem, Functor.ofSequence_map_homOfLE_succ] using
      (f i).naturality (homOfLE (Nat.le_succ m)))

/-- Evaluation of the glued system is the original full-chart gluing at that order. -/
theorem arithmeticLabeledSystemDesc_app (m : ℕ) :
    (arithmeticLabeledSystemDesc hπ data H k hk f hf).app m =
      (U m k hk).glueMorphisms (fun i => (f i).app m) (hf m) := rfl

attribute [local irreducible] arithmeticLabeledSystemDesc

/-- The assembled natural map recovers every original full labeled chart at every order. -/
@[reassoc] theorem arithmeticLabeledSystemDesc_chart (m : ℕ) (i : ArithmeticChartLabel k) :
    c m k hk i ≫ (arithmeticLabeledSystemDesc hπ data H k hk f hf).app m = (f i).app m := by
  rw [arithmeticLabeledSystemDesc_app]
  exact (U m k hk).ι_glueMorphisms _ _ i

/-- The entire chart natural transformation is retained by the assembled system map. -/
theorem arithmeticLabeledSystemDesc_chartSystem (i : ArithmeticChartLabel k) :
    arithmeticLabeledChartSystemMap hπ data H k hk i ≫
      arithmeticLabeledSystemDesc hπ data H k hk f hf = f i := by
  ext m
  exact arithmeticLabeledSystemDesc_chart hπ data H k hk f hf m i

/-- The full original chart systems detect maps out of the global arithmetic system. -/
theorem arithmeticLabeledSystem_hom_ext (g h : X ⟶ Y)
    (he : ∀ i, arithmeticLabeledChartSystemMap hπ data H k hk i ≫ g =
      arithmeticLabeledChartSystemMap hπ data H k hk i ≫ h) : g = h := by
  ext m
  apply (U m k hk).hom_ext
  intro i
  exact NatTrans.congr_app (he i) m

/-- No different global natural map has the same prescribed full chart restrictions. -/
theorem arithmeticLabeledSystemDesc_unique (g : X ⟶ Y)
    (hg : ∀ i, arithmeticLabeledChartSystemMap hπ data H k hk i ≫ g = f i) :
    g = arithmeticLabeledSystemDesc hπ data H k hk f hf := by
  apply arithmeticLabeledSystem_hom_ext hπ data H k hk
  intro i
  exact (hg i).trans (arithmeticLabeledSystemDesc_chartSystem hπ data H k hk f hf i).symm

end FLT.Mazur.WeierstrassDividedDepth
