/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedAtlasCover

/-!
# Every complete atlas-pair domain is the actual chart fiber product

The open domains of the full resolved-product cover are isomorphic to the
relative products of the corresponding smooth integral charts. Thus building
local addition on these products uses exactly the covered input schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "chart" => globalSmoothAtlasMap hπ data j hj

variable (a b : Fin (j + 3))
local notation "O" => finiteResolvedAtlasOpen hπ data j hj a b
local notation "ta" => chart a ≫ t
local notation "tb" => chart b ≫ t
local notation "left" => finiteResolvedAtlasLeft hπ data j hj a b
local notation "right" => finiteResolvedAtlasRight hπ data j hj a b

/-- The actual relative chart product maps openly into the resolved product. -/
def finiteResolvedAtlasPairInput : pullback ta tb ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.map ta tb t t (chart a) (chart b) (𝟙 _) (by simp) (by simp)

local notation "input" => finiteResolvedAtlasPairInput hπ data j hj a b

instance finiteResolvedAtlasPairInput_open : IsOpenImmersion input := by
  dsimp only [finiteResolvedAtlasPairInput]
  infer_instance

/-- The first projection is precisely the first actual chart inclusion. -/
@[reassoc] theorem finiteResolvedAtlasPairInput_fst :
    input ≫ pullback.fst t t = pullback.fst ta tb ≫ chart a := by
  simp only [finiteResolvedAtlasPairInput, pullback.map, pullback.lift_fst]

/-- The second projection is precisely the second actual chart inclusion. -/
@[reassoc] theorem finiteResolvedAtlasPairInput_snd :
    input ≫ pullback.snd t t = pullback.snd ta tb ≫ chart b := by
  simp only [finiteResolvedAtlasPairInput, pullback.map, pullback.lift_snd]

/-- Every point of the full relative chart product lies in its displayed open domain. -/
theorem finiteResolvedAtlasPairInput_range : Set.range input ⊆ O := by
  rintro _ ⟨x, rfl⟩
  constructor
  · exact ⟨pullback.fst ta tb x,
      (congrArg (fun f => f x) (finiteResolvedAtlasPairInput_fst hπ data j hj a b)).symm⟩
  · exact ⟨pullback.snd ta tb x,
      (congrArg (fun f => f x) (finiteResolvedAtlasPairInput_snd hπ data j hj a b)).symm⟩

/-- The whole chart product factors through the actual pair domain. -/
def finiteResolvedAtlasPairToOpen : pullback ta tb ⟶ (O).toScheme :=
  IsOpenImmersion.lift (O).ι input (by
    rw [Scheme.Opens.range_ι]
    exact finiteResolvedAtlasPairInput_range hπ data j hj a b)

local notation "toOpen" => finiteResolvedAtlasPairToOpen hπ data j hj a b

/-- Factoring through the pair open retains the original whole product map. -/
@[reassoc] theorem finiteResolvedAtlasPairToOpen_ι : toOpen ≫ (O).ι = input :=
  IsOpenImmersion.lift_fac _ _ _

/-- The pair open supplies its two actual chart-valued inputs. -/
def finiteResolvedAtlasOpenToPair : (O).toScheme ⟶ pullback ta tb :=
  pullback.lift left right (finiteResolvedAtlas_inputs_condition hπ data j hj a b)

local notation "toPair" => finiteResolvedAtlasOpenToPair hπ data j hj a b

/-- The two genuine chart inputs recover precisely the ambient pair inclusion. -/
@[reassoc] theorem finiteResolvedAtlasOpenToPair_input : toPair ≫ input = (O).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, finiteResolvedAtlasPairInput_fst, ← Category.assoc]
    change (pullback.lift left right _ ≫ pullback.fst ta tb) ≫ chart a = _
    rw [pullback.lift_fst, finiteResolvedAtlasLeft_chart]
  · rw [Category.assoc, finiteResolvedAtlasPairInput_snd, ← Category.assoc]
    change (pullback.lift left right _ ≫ pullback.snd ta tb) ≫ chart b = _
    rw [pullback.lift_snd, finiteResolvedAtlasRight_chart]

/-- Every domain in the full cover is exactly the relative product of its smooth charts. -/
def finiteResolvedAtlasPairIso : (O).toScheme ≅ pullback ta tb where
  hom := toPair
  inv := toOpen
  hom_inv_id := by
    apply (cancel_mono (O).ι).mp
    rw [Category.assoc, finiteResolvedAtlasPairToOpen_ι,
      finiteResolvedAtlasOpenToPair_input, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono input).mp
    rw [Category.assoc, finiteResolvedAtlasOpenToPair_input,
      finiteResolvedAtlasPairToOpen_ι, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
