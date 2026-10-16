/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeSeparation
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeBoundary

/-!
# Wrong initial arithmetic full-node labels have no Laurent intersection

The generic original node separation persists through the actual arithmetic
coefficient extension and its full original tensor comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "ha₀" => ha.map q
local notation "hs₀" => arithmeticCoefficient_mem π m hs
local notation "h2₀" => arithmeticCoefficient_mem π m h2
local notation "h3₀" => arithmeticCoefficient_mem π m h3
local notation "h4₀" => arithmeticCoefficient_mem π m h4
local notation "h6₀" => arithmeticCoefficient_mem π m h6
local notation "r₀" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  hJ ha₀ h2₀ h3₀ h4₀ h6₀
local notation "hr₀" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  hJ ha₀ h2₀ h3₀ h4₀ h6₀
local notation "hm₀" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  hJ ha₀ h2₀ h3₀ h4₀ h6₀
local notation "g₀" => laurentNodeRestriction (W.map q) (q s) (q b3) (q b4) (q b6) J
  hJ ha₀ hs₀ h2₀ h3₀ h4₀ h6₀
local notation "G" => arithmeticInitialNodeRestriction π m W s b3 b4 b6 ha h2 h3 h4 h6 hs
local notation "F" => arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "H" => arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "Fₜ" => arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "Hₜ" => arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "e" => arithmeticInitialTensorIso π m W s b3 b4 b6

/-- The complete small arithmetic Laurent boundary misses the full opposite tensor node. -/
theorem arithmeticSmallBoundary_oppositeNode_disjoint :
    Disjoint (Set.range (G ≫ Fₜ)) (Set.range Hₜ) := by
  have h : Disjoint (Set.range (G ≫ F)) (Set.range H) := by
    change Disjoint (Set.range (Spec.map (CommRingCat.ofHom (g₀).toRingHom) ≫
      polynomialNodeChart (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J hJ hm₀ h3₀)) _
    rw [laurentNodeRestriction_first_spec]
    exact smallLaurent_oppositeNode_disjoint (W.map q) (q s) (q b3) (q b4) (q b6) J
      hJ ha₀ hs₀ h2₀ h3₀ h4₀ h6₀ r₀ hm₀ hr₀
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have he : H y = (G ≫ F) x := (e).hom.homeomorph.injective hy
  exact Set.disjoint_left.mp h ⟨x, rfl⟩ ⟨y, he⟩

/-- The complete opposite arithmetic Laurent boundary misses the full first tensor node. -/
theorem arithmeticOppositeBoundary_firstNode_disjoint :
    Disjoint (Set.range (G ≫ Hₜ)) (Set.range Fₜ) := by
  have h : Disjoint (Set.range (G ≫ H)) (Set.range F) := by
    change Disjoint (Set.range (Spec.map (CommRingCat.ofHom (g₀).toRingHom) ≫
      polynomialOppositeNodeChart (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J hJ hm₀ h3₀)) _
    rw [laurentNodeRestriction_opposite_spec]
    exact oppositeLaurent_firstNode_disjoint (W.map q) (q s) (q b3) (q b4) (q b6) J
      hJ ha₀ hs₀ h2₀ h3₀ h4₀ h6₀ r₀ hm₀ hr₀
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have he : F y = (G ≫ H) x := (e).hom.homeomorph.injective hy
  exact Set.disjoint_left.mp h ⟨x, rfl⟩ ⟨y, he⟩

/-- A full initial Laurent boundary never lies in the wrong Boolean full-node chart. -/
theorem arithmeticInitialBoundary_crossLabel_disjoint (a b : Bool) (hab : a ≠ b) :
    Disjoint (Set.range (G ≫ (if a then Hₜ else Fₜ)))
      (Set.range (if b then Hₜ else Fₜ)) := by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact arithmeticSmallBoundary_oppositeNode_disjoint π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  · exact arithmeticOppositeBoundary_firstNode_disjoint π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  · exact (hab rfl).elim

end FLT.Mazur.WeierstrassModificationX
