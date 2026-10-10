/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueGeometry
public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas

/-!
# The complete Laurent infinity chart in the projective residue model

Normalize the retained infinity chart at every finite modification stage.
The exact indexed atlas object, full global image, residue structure and
original cubic contraction all survive the Laurent comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "e" => infinityResidueIso D hdepth
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The entire Laurent chart embeds through the original tensor infinity inclusion. -/
def infinityLaurentChart : Spec (.of K[T;T⁻¹]) ⟶ finiteGlobalTensorModel hπ data K j hj :=
  (e).hom ≫ finiteInfinityTensorChart hπ data K j hj

instance infinityLaurentChart_isOpenImmersion :
    IsOpenImmersion (infinityLaurentChart hπ data D hdepth j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The Laurent chart covers exactly the full original infinity tensor chart. -/
theorem infinityLaurentChart_range :
    Set.range (infinityLaurentChart hπ data D hdepth j hj) =
      Set.range (finiteInfinityTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(e).hom x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (e).hom.homeomorph.surjective x
    exact ⟨y, congrArg (finiteInfinityTensorChart hπ data K j hj) hy⟩

/-- The full original projective cubic contraction retains its Laurent functions. -/
@[reassoc] theorem infinityLaurentChart_toCurve :
    infinityLaurentChart hπ data D hdepth j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj = infinityResidueContraction D hdepth := by
  rw [infinityLaurentChart, Category.assoc, finiteInfinityTensorChart_toCurve]
  exact infinityResidueIso_contraction D hdepth

/-- The actual global Laurent chart retains the residue coefficient structure. -/
@[reassoc] theorem infinityLaurentChart_structure :
    infinityLaurentChart hπ data D hdepth j hj ≫ pullback.fst _ _ =
      (MultiplicativeGroupScheme.gm K).hom := by
  rw [infinityLaurentChart, Category.assoc, finiteInfinityTensorChart_structure]
  exact infinityResidueIso_structure D hdepth

/-- The entire normalized infinity chart is the original zeroth indexed atlas object. -/
def infinityLaurentAtlasIso : Spec (.of K[T;T⁻¹]) ≅
    globalTensorAtlasObject hπ data K j hj 0 := e

/-- Its exact zeroth atlas map remains the actual projective inclusion. -/
@[reassoc] theorem infinityLaurentAtlasIso_map :
    (infinityLaurentAtlasIso hπ data D hdepth j hj).hom ≫
      globalTensorAtlasMap hπ data K j hj 0 = infinityLaurentChart hπ data D hdepth j hj := rfl

end FLT.Mazur.WeierstrassDividedDepth
