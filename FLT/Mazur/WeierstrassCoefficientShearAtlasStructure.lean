/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlas

/-!
# Coefficient structure of the complete sheared equation atlas

Each full equation has its usual structure morphism to the extended coefficient
spectrum. These actual morphisms agree on the whole pairwise intersections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (t : ℕ) (ht : t ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "a" => coefficientShearAtlasMap hπ data S r t ht

omit hπ in
/-- The usual extended coefficient map of each full affine equation. -/
def coefficientShearAtlasStructure (i : Fin 3 ⊕ Fin t) :
    coefficientShearAtlasObject data S r t ht i ⟶ Spec (.of S) :=
  match i with
  | .inl i => Fin.cases (Spec.map (CommRingCat.ofHom (algebraMap S _)))
      (Fin.cases (Spec.map (CommRingCat.ofHom (algebraMap S _)))
        (fun _ => Spec.map (CommRingCat.ofHom (algebraMap S _)))) i
  | .inr _ => Spec.map (CommRingCat.ofHom (algebraMap S _))

/-- Every actual chart embedding retains its full extended coefficient map. -/
@[reassoc] theorem coefficientShearAtlasMap_structure (i : Fin 3 ⊕ Fin t) :
    a i ≫ pullback.fst q (finiteGlobalStructure hπ data t ht) =
      coefficientShearAtlasStructure data S r t ht i := by
  rcases i with i | j
  · fin_cases i
    · exact finiteInfinityTensorChart_structure hπ data S t ht
    · exact globalDividedCoefficientShearChart_structure hπ data S r t ht
    · exact globalInitialCoefficientShearChart_structure hπ data S r t ht
  · exact retainedCoefficientShearChart_structure hπ data S r t ht j.val (by omega)

/-- The ordinary coefficient maps agree on the entire scheme-theoretic chart intersections. -/
@[reassoc] theorem coefficientShearAtlasStructure_overlap (i j : Fin 3 ⊕ Fin t) :
    pullback.fst (a i) (a j) ≫ coefficientShearAtlasStructure data S r t ht i =
      pullback.snd (a i) (a j) ≫ coefficientShearAtlasStructure data S r t ht j := by
  rw [← coefficientShearAtlasMap_structure, ← coefficientShearAtlasMap_structure,
    pullback.condition_assoc]

end FLT.Mazur.WeierstrassDividedDepth
