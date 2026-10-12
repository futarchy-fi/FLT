/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlas

/-!
# Comparison with the entire original indexed tensor atlas

The comparison is over the original global model, so it retains both original
projections. On the divided and incidence charts it is the explicit coefficient/shear map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- The original tensor index for each actual sheared coefficient equation. -/
def coefficientShearAtlasIndex (t : ℕ) : Fin 3 ⊕ Fin t → Fin (t + 3) :=
  Sum.elim (Fin.cases 0 (Fin.cases 1 (fun _ => ⟨t + 2, by omega⟩)))
    (fun j => ⟨t - j.val + 1, by omega⟩)

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (t : ℕ) (ht : t ≤ n)

/-- Every new full chart occupies exactly its corresponding original indexed open. -/
theorem coefficientShearAtlasMap_range (i : Fin 3 ⊕ Fin t) :
    Set.range (coefficientShearAtlasMap hπ data S r t ht i) =
      Set.range (globalTensorAtlasMap hπ data S t ht (coefficientShearAtlasIndex t i)) := by
  rcases i with i | j
  · fin_cases i
    · rfl
    · exact globalDividedCoefficientShearChart_range_index hπ data S r t ht
    · exact globalInitialCoefficientShearChart_range_index hπ data S r t ht
  · exact retainedCoefficientShearChart_range_index hπ data S r t ht j.val (by omega)

/-- The actual coefficient equations identify the full original indexed tensor charts. -/
def coefficientShearAtlasIso (i : Fin 3 ⊕ Fin t) :
    coefficientShearAtlasObject data S r t ht i ≅
      globalTensorAtlasObject hπ data S t ht (coefficientShearAtlasIndex t i) :=
  IsOpenImmersion.isoOfRangeEq _ _ (coefficientShearAtlasMap_range hπ data S r t ht i)

/-- The entire comparison preserves the chart embedding, not just its point-set range. -/
@[reassoc] theorem coefficientShearAtlasIso_map (i : Fin 3 ⊕ Fin t) :
    (coefficientShearAtlasIso hπ data S r t ht i).hom ≫
      globalTensorAtlasMap hπ data S t ht (coefficientShearAtlasIndex t i) =
        coefficientShearAtlasMap hπ data S r t ht i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The infinity comparison is the identity on the original tensor algebra. -/
theorem coefficientShearAtlasIso_infinity :
    (coefficientShearAtlasIso hπ data S r t ht (.inl 0)).hom = 𝟙 _ := by
  apply (cancel_mono (finiteInfinityTensorChart hπ data S t ht)).mp
  rw [Category.id_comp]
  exact coefficientShearAtlasIso_map hπ data S r t ht (.inl 0)

local notation "d" => data (Fin.mk t (Nat.lt_succ_of_le ht))
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))

/-- On the divided chart the comparison is exactly the full algebraic shear isomorphism. -/
theorem coefficientShearAtlasIso_divided :
    (coefficientShearAtlasIso hπ data S r t ht (.inl 1)).hom =
      (dividedCoefficientShearIso W (π ^ (start + t))
        (Data.b3 d) (Data.b4 d) (Data.b6 d) S r).hom ≫
          (finiteDividedTensorAtlasIso hπ data S t ht).hom := by
  apply (cancel_mono (globalTensorAtlasMap hπ data S t ht 1)).mp
  trans coefficientShearAtlasMap hπ data S r t ht (.inl 1)
  · exact coefficientShearAtlasIso_map hπ data S r t ht (.inl 1)
  rw [Category.assoc]
  change _ = _ ≫ _ ≫ (finiteTensorAtlasMap hπ data S t ht 0 ≫ _)
  rw [← Category.assoc (finiteDividedTensorAtlasIso hπ data S t ht).hom,
    finiteDividedTensorAtlasIso_map]
  rfl

/-- On the incidence chart the comparison is exactly the full algebraic shear isomorphism. -/
theorem coefficientShearAtlasIso_initial :
    (coefficientShearAtlasIso hπ data S r t ht (.inl 2)).hom =
      (incidenceCoefficientShearIso W (π ^ start)
        (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) S r).hom ≫
          (finiteInitialTensorAtlasIso hπ data S t ht).hom := by
  apply (cancel_mono (globalTensorAtlasMap hπ data S t ht ⟨t + 2, by omega⟩)).mp
  trans coefficientShearAtlasMap hπ data S r t ht (.inl 2)
  · exact coefficientShearAtlasIso_map hπ data S r t ht (.inl 2)
  rw [Category.assoc]
  exact congrArg (fun f => (incidenceCoefficientShearIso W (π ^ start)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) S r).hom ≫ f)
    (globalInitialTensorChart_eq_index hπ data S t ht).symm

end FLT.Mazur.WeierstrassDividedDepth
