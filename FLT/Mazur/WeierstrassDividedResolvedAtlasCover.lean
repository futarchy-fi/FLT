/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSmoothAtlas
public import FLT.Mazur.WeierstrassDividedResolvedProductOpens

/-!
# All chart pairs cover the entire resolved smooth product

Use full smooth restrictions of the actual integral atlas, including the
older X-charts. Each pair domain has two genuine chart-valued input maps.
The cover makes no assertion that an addition formula is defined everywhere.
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

/-- The full open where the two resolved inputs lie in the two indicated charts. -/
def finiteResolvedAtlasOpen (a b : Fin (j + 3)) :
    (finiteResolvedProduct hπ data j hj).Opens :=
  pullback.fst t t ⁻¹ᵁ (chart a).opensRange ⊓ pullback.snd t t ⁻¹ᵁ (chart b).opensRange

/-- Every actual resolved smooth pair lies in a displayed pair domain. -/
theorem finiteResolvedAtlasOpen_covers (z : finiteResolvedProduct hπ data j hj) :
    ∃ a b, z ∈ finiteResolvedAtlasOpen hπ data j hj a b := by
  obtain ⟨a, x, hx⟩ := globalSmoothAtlas_cover hπ data j hj (pullback.fst t t z)
  obtain ⟨b, y, hy⟩ := globalSmoothAtlas_cover hπ data j hj (pullback.snd t t z)
  exact ⟨a, b, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩

/-- These full chart-pair domains form an open cover of the entire relative product. -/
def finiteResolvedAtlasCover : (finiteResolvedProduct hπ data j hj).OpenCover where
  I₀ := Fin (j + 3) × Fin (j + 3)
  X ab := (finiteResolvedAtlasOpen hπ data j hj ab.1 ab.2).toScheme
  f ab := (finiteResolvedAtlasOpen hπ data j hj ab.1 ab.2).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun ab => inferInstance⟩
    intro z
    obtain ⟨a, b, hz⟩ := finiteResolvedAtlasOpen_covers hπ data j hj z
    exact ⟨(a, b), ⟨z, hz⟩, rfl⟩

variable (a b : Fin (j + 3))
local notation "O" => finiteResolvedAtlasOpen hπ data j hj a b

/-- The full first input factors through its actual smooth integral chart. -/
def finiteResolvedAtlasLeft : (O).toScheme ⟶
    (globalSmoothAtlasOpen hπ data j hj a).toScheme :=
  IsOpenImmersion.lift (chart a) ((O).ι ≫ pullback.fst t t) (by
    rintro _ ⟨x, rfl⟩
    exact x.property.1)

/-- The full second input factors through its actual smooth integral chart. -/
def finiteResolvedAtlasRight : (O).toScheme ⟶
    (globalSmoothAtlasOpen hπ data j hj b).toScheme :=
  IsOpenImmersion.lift (chart b) ((O).ι ≫ pullback.snd t t) (by
    rintro _ ⟨x, rfl⟩
    exact x.property.2)

/-- The lifted first chart input is the original resolved first projection. -/
@[reassoc] theorem finiteResolvedAtlasLeft_chart :
    finiteResolvedAtlasLeft hπ data j hj a b ≫ chart a = (O).ι ≫ pullback.fst t t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lifted second chart input is the original resolved second projection. -/
@[reassoc] theorem finiteResolvedAtlasRight_chart :
    finiteResolvedAtlasRight hπ data j hj a b ≫ chart b = (O).ι ≫ pullback.snd t t :=
  IsOpenImmersion.lift_fac _ _ _

/-- Both genuine chart-valued inputs retain the same original coefficient point. -/
theorem finiteResolvedAtlas_inputs_condition :
    finiteResolvedAtlasLeft hπ data j hj a b ≫ chart a ≫ t =
      finiteResolvedAtlasRight hπ data j hj a b ≫ chart b ≫ t := by
  rw [finiteResolvedAtlasLeft_chart_assoc, finiteResolvedAtlasRight_chart_assoc,
    pullback.condition]

/-- Equality on all actual chart-pair domains detects equality on the entire product. -/
theorem finiteResolvedAtlas_hom_ext {Z : Scheme}
    (f g : finiteResolvedProduct hπ data j hj ⟶ Z)
    (h : ∀ a b, (finiteResolvedAtlasOpen hπ data j hj a b).ι ≫ f =
      (finiteResolvedAtlasOpen hπ data j hj a b).ι ≫ g) : f = g := by
  apply (finiteResolvedAtlasCover hπ data j hj).hom_ext
  intro ab
  exact h ab.1 ab.2

end FLT.Mazur.WeierstrassDividedDepth
