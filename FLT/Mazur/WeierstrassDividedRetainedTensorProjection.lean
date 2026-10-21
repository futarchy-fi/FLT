/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedOlderCoordinates
public import FLT.Mazur.WeierstrassDividedArithmeticTargetPairSpectrum
public import FLT.Mazur.WeierstrassDividedTensorIntegralAtlas
public import FLT.Mazur.WeierstrassDividedSuccessiveTensorCoordinates

/-!
# Retained tensor coordinates project to the original integral chart

The comparison preserves the entire integral chart, before any smooth or
addition-domain restriction. The own-depth lower contraction is unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (a : ℕ) (ha : a < k)
local notation "idx" => retainedOlderFormulaIndex k a ha
local notation "Q" => Quotient R π m
local notation "e" => data ⟨a + 1, by omega⟩

omit [IsBezout R] in
/-- Lowering a retained chart to its own preceding depth adds no extra contraction. -/
theorem retainedOlderLowerCoordinates_self :
    retainedOlderLowerCoordinates hπ data k hk a ha a le_rfl =
      retainedOlderFormulaCoordinates hπ data k hk a ha := by
  unfold retainedOlderLowerCoordinates depthTransitionMorphism
  rw [depthTransition_self]
  change _ ≫ Spec.map (𝟙 _) = _
  rw [Spec.map_id, Category.comp_id]

omit [IsBezout R] in
/-- The indexed tensor isomorphism retains the full original integral projection. -/
@[reassoc] theorem arithmeticRetainedTensorIso_projection :
    (arithmeticRetainedTensorIso hπ data m k hk a ha).hom ≫
      tensorIntegralAtlasProjection hπ data Q k hk idx ≫
        eqToHom (retainedOlderFormulaObject_eq data k hk a ha) =
      (TensorOpenChart.projection : Spec (.of (WeierstrassSuccessiveX.ScalarExtension
        W (π ^ (start + a)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) Q)) ⟶ stepX e) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr ha)
  have hs : a + 1 + r - (a + 1) = r := by omega
  have hi : a + 1 + r - a = r + 1 := by omega
  change (arithmeticRetainedTensorIso hπ data m (a + 1 + r) hk a ha).hom ≫
    pullback.fst _ _ ≫ eqToHom _ = _
  dsimp only [arithmeticRetainedTensorIso]
  simp only [Iso.trans_hom, eqToIso.hom]
  generalize_proofs
  generalize hs' : a + 1 + r - (a + 1) = r' at *
  clear hs'
  subst r'
  generalize hi' : a + 1 + r - a = i at *
  have he : i = r + 1 := by omega
  clear hi'
  subst i
  simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc]
  unfold olderSuccessiveTensorAtlasIso
  rw [(olderSuccessiveTensorChart_index_isPullback
    hπ data Q a (by omega) r hk).flip.isoPullback_hom_fst]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

local notation "d" => data ⟨a, by omega⟩

omit [IsBezout R] in
/-- Undoing the full tensor indexing recovers exactly the integral own-depth contraction. -/
@[reassoc] theorem arithmeticRetainedTensorIso_contraction :
    (arithmeticRetainedTensorIso hπ data m k hk a ha).inv ≫
      Spec.map (CommRingCat.ofHom (successiveTensorInput hπ d e Q).toRingHom) =
        tensorIntegralAtlasProjection hπ data Q k hk idx ≫
          retainedOlderLowerCoordinates hπ data k hk a ha a le_rfl := by
  apply (cancel_epi (arithmeticRetainedTensorIso hπ data m k hk a ha).hom).mp
  rw [Iso.hom_inv_id_assoc, retainedOlderLowerCoordinates_self,
    retainedOlderFormulaCoordinates,
    arithmeticRetainedTensorIso_projection_assoc, successiveTensorInput_spec]

end FLT.Mazur.WeierstrassDividedDepth
