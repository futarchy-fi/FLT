/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticInitialCover
public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators

/-!
# Both full initial nodes on the original arithmetic tensor scheme

The original tensor base-change equivalence transports the two constructed
node charts and their joint coverage, retaining the original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => ExtendedCoordinate W s b3 b4 b6 Q
local notation "T₀" => Q ⊗[R] A
local notation "L" => PolynomialNodeOpen (W.map q) (q s)

/-- The original tensor comparison on the entire initial arithmetic scheme. -/
def arithmeticInitialTensorIso : Spec (.of B) ≅ Spec (.of T₀) :=
  Scheme.Spec.mapIso (baseChangeEquiv W s b3 b4 b6 Q).toRingEquiv.toCommRingCatIso.op

/-- The full original tensor isomorphism preserves the arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticInitialTensorIso_structure :
    (arithmeticInitialTensorIso π m W s b3 b4 b6).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q T₀)) =
        Spec.map (CommRingCat.ofHom (algebraMap Q B)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (baseChangeEquiv W s b3 b4 b6 Q).commutes z

variable (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "F" => arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "G" => arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
local notation "e" => arithmeticInitialTensorIso π m W s b3 b4 b6

/-- The first full initial node is an actual chart of the original tensor scheme. -/
def arithmeticInitialTensorNodeChart : Spec (.of L) ⟶ Spec (.of T₀) := F ≫ (e).hom

/-- The opposite full initial node is an actual chart of the same original tensor scheme. -/
def arithmeticOppositeInitialTensorNodeChart : Spec (.of L) ⟶ Spec (.of T₀) := G ≫ (e).hom

/-- The first original tensor chart is an open immersion. -/
theorem arithmeticInitialTensorNodeChart_isOpenImmersion :
    IsOpenImmersion (arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) := by
  let _ := arithmeticInitialNodeChart_isOpenImmersion π m W s b3 b4 b6 ha h2 h3 h4 h6
  unfold arithmeticInitialTensorNodeChart
  infer_instance

/-- The opposite original tensor chart is an open immersion. -/
theorem arithmeticOppositeInitialTensorNodeChart_isOpenImmersion :
    IsOpenImmersion
      (arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) := by
  let _ := arithmeticOppositeInitialNodeChart_isOpenImmersion π m W s b3 b4 b6 ha h2 h3 h4 h6
  unfold arithmeticOppositeInitialTensorNodeChart
  infer_instance

/-- The first original tensor chart retains its arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticInitialTensorNodeChart_structure :
    arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q T₀)) =
        Spec.map (CommRingCat.ofHom (algebraMap Q L)) := by
  rw [arithmeticInitialTensorNodeChart, Category.assoc,
    arithmeticInitialTensorIso_structure, arithmeticInitialNodeChart_structure]

/-- The opposite original tensor chart retains the same coefficient morphism. -/
@[reassoc] theorem arithmeticOppositeInitialTensorNodeChart_structure :
    arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q T₀)) =
        Spec.map (CommRingCat.ofHom (algebraMap Q L)) := by
  rw [arithmeticOppositeInitialTensorNodeChart, Category.assoc,
    arithmeticInitialTensorIso_structure, arithmeticOppositeInitialNodeChart_structure]

/-- Both constructed full nodes cover the original arithmetic tensor scheme at every order. -/
theorem arithmeticInitialTensorNodeCharts_cover (p : Spec (.of T₀)) :
    p ∈ Set.range (arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ∨
      p ∈ Set.range
        (arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) := by
  obtain h | h := arithmeticInitialNodeCharts_cover π m W s b3 b4 b6 ha h2 h3 h4 h6 ((e).inv p)
  · obtain ⟨z, hz⟩ := h
    left
    refine ⟨z, ?_⟩
    change (e).hom (F z) = p
    rw [hz]
    exact congrArg (fun f ↦ f p) (e).inv_hom_id
  · obtain ⟨z, hz⟩ := h
    right
    refine ⟨z, ?_⟩
    change (e).hom (G z) = p
    rw [hz]
    exact congrArg (fun f ↦ f p) (e).inv_hom_id

end FLT.Mazur.WeierstrassModificationX
