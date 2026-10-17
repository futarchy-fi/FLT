/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualDecomposition
public import FLT.Mazur.EquivalenceRelationChartFamilyCorrections

/-!
# Exact independent-chart equations on the exhaustive mixed branch product

Each pair keeps its own frame sizes, labels, and full residual coefficient ring.
A simultaneous family satisfies the original equations exactly when its same
sections satisfy every retained branch equation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
local notation "M" => mixedChartOpen o o' U V

/-- Each coefficient factor is an original residual or embedding branch ring. -/
abbrev mixedBranchCoordinates :=
  ∀ a : Option (J ↪ I), Γ((mixedResidualBranchOpen e o o' (M).ι a).toScheme, ⊤)

/-- The actual product restriction, with no quotient or reduced coefficient rings. -/
def mixedBranchCoefficientMap : Γ((M).toScheme, ⊤) →+*
    mixedBranchCoordinates e o o' U V :=
  (mixedResidualBranchSectionsIso e o o' (M).ι).hom.hom

/-- Every coordinate of the product map is the actual open restriction. -/
theorem mixedBranchCoefficientMap_apply (t : Γ((M).toScheme, ⊤)) (a : Option (J ↪ I)) :
    mixedBranchCoefficientMap e o o' U V t a =
      (mixedResidualBranchOpen e o o' (M).ι a).ι.appTop t :=
  mixedResidualBranchSectionsIso_apply e o o' (M).ι t a

/-- Every collection of branch coefficients glues uniquely to the full mixed relation. -/
theorem mixedBranchCoefficientMap_bijective :
    Function.Bijective (mixedBranchCoefficientMap e o o' U V) :=
  ConcreteCategory.bijective_of_isIso (mixedResidualBranchSectionsIso e o o' (M).ι).hom

/-- Actual projection from a retained branch to the independent first chart. -/
def mixedBranchFirst (a : Option (J ↪ I)) :
    (mixedResidualBranchOpen e o o' (M).ι a).toScheme ⟶ U.toScheme :=
  (mixedResidualBranchOpen e o o' (M).ι a).ι ≫ mixedChartFirst o o' U V

/-- Actual projection from the same branch to the independent second chart. -/
def mixedBranchSecond (a : Option (J ↪ I)) :
    (mixedResidualBranchOpen e o o' (M).ι a).toScheme ⟶ V.toScheme :=
  (mixedResidualBranchOpen e o o' (M).ι a).ι ≫ mixedChartSecond o o' U V

/-- The exact original mixed equation keeps both the residual and all embedding equations. -/
theorem mixedChart_compatible_iff_branches (u : Γ(U.toScheme, ⊤))
    (v : Γ(V.toScheme, ⊤)) :
    (mixedChartFirst o o' U V).appTop u = (mixedChartSecond o o' U V).appTop v ↔
      ∀ a : Option (J ↪ I), (mixedBranchFirst e o o' U V a).appTop u =
        (mixedBranchSecond e o o' U V a).appTop v := by
  rw [mixedResidualBranch_sections_eq_iff e o o' (M).ι]
  simp only [mixedBranchFirst, mixedBranchSecond, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

namespace ChartFamily
variable {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ U a = U a)
  [∀ a, (source p q (Fin (n a)) (o a)).IsSeparated]

/-- All pairs use the same invariant chart family when testing their independent branches. -/
theorem difference_eq_zero_iff_branches (s : Sections e n o U hU) :
    difference e n o U hU s = 0 ↔ ∀ a b (c : Option (Fin (n b) ↪ Fin (n a))),
      (mixedBranchFirst e (o a) (o b) (U a) (U b) c).appTop (s a).val =
        (mixedBranchSecond e (o a) (o b) (U a) (U b) c).appTop (s b).val := by
  constructor
  · intro h a b
    apply (mixedChart_compatible_iff_branches e (o a) (o b) (U a) (U b) _ _).mp
    exact sub_eq_zero.mp (congrFun (congrFun h a) b)
  · intro h
    funext a b
    exact sub_eq_zero.mpr
      ((mixedChart_compatible_iff_branches e (o a) (o b) (U a) (U b) _ _).mpr (h a b))

end ChartFamily
end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
