/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroNodeMaps
public import FLT.Mazur.WeierstrassSuccessiveXZeroContraction

/-!
# The two full node charts of the zero-depth tensor fiber

The original node maps give an open cover and preserve the residue-field structure.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "ha" => D.a₁_unit.map (residue R)
open WeierstrassModificationX
local notation "L₀" => FullNodeOpen a c
local notation "L₁" => FullNodeOpen (-a) c
local notation "E" => zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

local notation "V" => zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4

/-- The first full node chart retains the original tensor target. -/
def zeroFirstNodeChart : Spec (.of L₀) ⟶ Spec (.of T) :=
  fullFirstNodeChart a c ha ≫ (V).hom

instance zeroFirstNodeChart_isOpenImmersion :
    IsOpenImmersion (zeroFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The first chart is induced by its original coordinate map. -/
theorem zeroFirstNodeChart_eq_spec :
    zeroFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) := by
  rw [zeroFirstNodeChart, fullFirstNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The first full node retains the actual residue-field structure. -/
@[reassoc] theorem zeroFirstNodeChart_structure :
    zeroFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L₀)) := by
  rw [zeroFirstNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  ext x
  exact (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4).commutes x

/-- The second full node chart retains the original tensor target. -/
def zeroSecondNodeChart : Spec (.of L₁) ⟶ Spec (.of T) :=
  fullSecondNodeChart a c ha ≫ (V).hom

instance zeroSecondNodeChart_isOpenImmersion :
    IsOpenImmersion (zeroSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The second chart is induced by its original coordinate map. -/
theorem zeroSecondNodeChart_eq_spec :
    zeroSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) := by
  rw [zeroSecondNodeChart, fullSecondNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second full node retains the actual residue-field structure. -/
@[reassoc] theorem zeroSecondNodeChart_structure :
    zeroSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L₁)) := by
  rw [zeroSecondNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  ext x
  exact (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4).commutes x

/-- Every point of the original tensor fiber lies in one of the full node neighborhoods. -/
theorem zeroNodeCharts_cover (z : Spec (.of T)) :
    z ∈ Set.range (zeroFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4) ∨
      z ∈ Set.range (zeroSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4) := by
  rcases fullNodeCharts_cover a c ha ((V).inv z) with ⟨x, hx⟩ | ⟨x, hx⟩
  · left
    refine ⟨x, ?_⟩
    change (V).hom (fullFirstNodeChart a c ha x) = z
    rw [hx]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  · right
    refine ⟨x, ?_⟩
    change (V).hom (fullSecondNodeChart a c ha x) = z
    rw [hx]
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl

end FLT.Mazur.WeierstrassSuccessiveX
