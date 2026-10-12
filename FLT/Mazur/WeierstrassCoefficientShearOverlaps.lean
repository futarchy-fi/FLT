/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlasComparison
public import FLT.Mazur.SchemeChartOverlapComparison

/-!
# Full coefficient shear intersections and transitions

Every pair of actual sheared equations has precisely the original tensor
intersection, with both projection morphisms and exchange transitions retained.
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
local notation "a" => coefficientShearAtlasMap hπ data S r t ht
local notation "b" => fun i => globalTensorAtlasMap hπ data S t ht
  (coefficientShearAtlasIndex t i)
local notation "e" => coefficientShearAtlasIso hπ data S r t ht

/-- All full intersections identify with those of the original tensor atlas. -/
def coefficientShearOverlapIso (i j : Fin 3 ⊕ Fin t) :
    pullback (a i) (a j) ≅ pullback (b i) (b j) :=
  SchemeChartOverlapComparison.overlapIso _ _ _ _ (e i) (e j)
    (coefficientShearAtlasIso_map hπ data S r t ht i)
    (coefficientShearAtlasIso_map hπ data S r t ht j)

/-- The first projection retains its entire actual coefficient/shear chart morphism. -/
@[reassoc] theorem coefficientShearOverlapIso_fst (i j : Fin 3 ⊕ Fin t) :
    (coefficientShearOverlapIso hπ data S r t ht i j).hom ≫ pullback.fst (b i) (b j) =
      pullback.fst (a i) (a j) ≫ (e i).hom :=
  SchemeChartOverlapComparison.overlapIso_fst _ _ _ _ _ _ _ _

/-- The second projection retains its entire actual coefficient/shear chart morphism. -/
@[reassoc] theorem coefficientShearOverlapIso_snd (i j : Fin 3 ⊕ Fin t) :
    (coefficientShearOverlapIso hπ data S r t ht i j).hom ≫ pullback.snd (b i) (b j) =
      pullback.snd (a i) (a j) ≫ (e j).hom :=
  SchemeChartOverlapComparison.overlapIso_snd _ _ _ _ _ _ _ _

/-- The original transition obtained by exchanging charts is preserved as a scheme map. -/
@[reassoc] theorem coefficientShearOverlapIso_transition (i j : Fin 3 ⊕ Fin t) :
    (coefficientShearOverlapIso hπ data S r t ht i j).hom ≫
        (pullbackSymmetry (b i) (b j)).hom =
      (pullbackSymmetry (a i) (a j)).hom ≫
        (coefficientShearOverlapIso hπ data S r t ht j i).hom :=
  SchemeChartOverlapComparison.overlapIso_symmetry _ _ _ _ _ _ _ _

/-- Every original global-model morphism is retained on the full intersections. -/
@[reassoc] theorem coefficientShearOverlapIso_over (i j : Fin 3 ⊕ Fin t)
    {Y : Scheme.{u}} (g : finiteGlobalTensorModel hπ data S t ht ⟶ Y) :
    (coefficientShearOverlapIso hπ data S r t ht i j).hom ≫
        pullback.fst (b i) (b j) ≫ b i ≫ g =
      pullback.fst (a i) (a j) ≫ a i ≫ g :=
  SchemeChartOverlapComparison.overlapIso_over _ _ _ _ _ _ _ _ g

end FLT.Mazur.WeierstrassDividedDepth
