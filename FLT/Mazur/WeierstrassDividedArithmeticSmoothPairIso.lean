/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairInclusion

/-!
# The two full smooth arithmetic pair presentations

The smooth open of the full chart product is isomorphic to the product of
the smooth chart opens. Both directions preserve the entire original pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (a b : Fin (k + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local notation "fa" => (O a).ι ≫ f
local notation "fb" => (O b).ι ≫ g
local notation "inc" => arithmeticSmoothPairInclusion hπ data m k hk a b
local notation "D" => arithmeticAtlasTestOpen hπ data m k hk a b
  (pullback.fst f g) (pullback.snd f g)
local notation "T" => arithmeticAtlasTestPair hπ data m k hk a b
  (pullback.fst f g) (pullback.snd f g) pullback.condition

/-- The inclusion lands in the simultaneous full smooth preimage. -/
theorem arithmeticSmoothPairInclusion_mem (p : (pullback fa fb : Scheme)) :
    inc p ∈ D := by
  constructor
  · change pullback.fst f g (inc p) ∈ O a
    have h := congrArg (fun morphism => morphism p)
      (arithmeticSmoothPairInclusion_first hπ data m k hk a b)
    exact h.symm ▸ (pullback.fst fa fb p).property
  · change pullback.snd f g (inc p) ∈ O b
    have h := congrArg (fun morphism => morphism p)
      (arithmeticSmoothPairInclusion_second hπ data m k hk a b)
    exact h.symm ▸ (pullback.snd fa fb p).property

/-- Regard the smooth product as a point of the full product's smooth open. -/
def arithmeticSmoothPairToOpen : pullback fa fb ⟶ (D).toScheme :=
  IsOpenImmersion.lift (D).ι inc (by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨inc p, arithmeticSmoothPairInclusion_mem hπ data m k hk a b p⟩, rfl⟩)

local notation "lift" => arithmeticSmoothPairToOpen hπ data m k hk a b

/-- The reverse presentation map retains both original inputs as whole morphisms. -/
@[reassoc] theorem arithmeticSmoothPairToOpen_inclusion : lift ≫ (D).ι = inc :=
  IsOpenImmersion.lift_fac _ _ _

/-- The two entire smooth domains are canonically isomorphic over the original pair. -/
def arithmeticSmoothPairIso : (D).toScheme ≅ pullback fa fb where
  hom := T
  inv := lift
  hom_inv_id := by
    apply (cancel_mono (D).ι).mp
    rw [Category.assoc, arithmeticSmoothPairToOpen_inclusion,
      arithmeticAtlasTestPair_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono inc).mp
    rw [Category.assoc, arithmeticAtlasTestPair_inclusion,
      arithmeticSmoothPairToOpen_inclusion, Category.id_comp]

/-- The forward isomorphism retains the complete original pair. -/
@[reassoc] theorem arithmeticSmoothPairIso_hom_inclusion :
    (arithmeticSmoothPairIso hπ data m k hk a b).hom ≫ inc = (D).ι :=
  arithmeticAtlasTestPair_inclusion hπ data m k hk a b

/-- The reverse isomorphism retains the complete original pair. -/
@[reassoc] theorem arithmeticSmoothPairIso_inv_inclusion :
    (arithmeticSmoothPairIso hπ data m k hk a b).inv ≫ (D).ι = inc :=
  arithmeticSmoothPairToOpen_inclusion hπ data m k hk a b

local instance arithmeticSmoothPairIso_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The smooth open is also the preimage of the actual arithmetic smooth loci. -/
theorem arithmeticSmoothPairOpen_relative :
    D = (pullback.fst f g ≫ chart a) ⁻¹ᵁ (s).smoothLocus ⊓
      (pullback.snd f g ≫ chart b) ⁻¹ᵁ (s).smoothLocus := by
  unfold arithmeticAtlasTestOpen
  rw [arithmeticAtlasSmoothOpen_relative, arithmeticAtlasSmoothOpen_relative,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]

end FLT.Mazur.WeierstrassDividedDepth
