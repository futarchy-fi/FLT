/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalSections
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# The full original initial conic parameters at every retained stage

These actual affine parameter maps retain both initial ordered nodes and the
residue-field structure. They supply the conic halves of the first components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data j hj

local notation "g" => initialGlobalResidueFiberChart hπ data D j hj hstart hk
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c)))

/-- The entire original initial conic retained in the global fiber. -/
def initialGlobalConic := fiberConicImmersion a c ≫ g

/-- The full initial conic keeps its coefficient structure. -/
@[reassoc] theorem initialGlobalConic_structure :
    initialGlobalConic hπ data D j hj hstart hk ≫ pullback.fst q f = conicStructure a c := by
  rw [initialGlobalConic, Category.assoc, initialGlobalResidueFiberChart_structure]
  exact terminalComponent_algebra_structure (fiberConicMap a c)

/-- The original first complete parameter, including its initial node origin. -/
def initialGlobalConicFirstParameter :=
  (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫
    initialGlobalConic hπ data D j hj hstart hk

/-- The first conic marking is exactly the original initial section. -/
@[reassoc] theorem initialGlobalFirstSection_conic :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫
      initialGlobalConic hπ data D j hj hstart hk =
        initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialGlobalConic, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp, initialGlobalFirstSection, fullFirstIncidencePoint_conic]
  rfl

/-- The entire first parameter retains the original initial node at its origin. -/
@[reassoc] theorem initialGlobalConicFirstParameter_origin :
    o ≫ initialGlobalConicFirstParameter hπ data D j hj hstart hk =
      initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialGlobalConicFirstParameter, conicFirstParameterIso_origin_assoc,
    initialGlobalFirstSection_conic]

/-- The complete first initial parameter is over the original residue field. -/
@[reassoc] theorem initialGlobalConicFirstParameter_structure :
    initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫ pullback.fst q f = b := by
  rw [initialGlobalConicFirstParameter]
  simp only [Category.assoc, initialGlobalConic_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c))]
  exact terminalComponent_algebra_structure (conicFirstParameterEquiv a c ha).symm.toAlgHom

/-- The original second complete parameter, including its initial node origin. -/
def initialGlobalConicSecondParameter :=
  (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫
    initialGlobalConic hπ data D j hj hstart hk

/-- The second conic marking is exactly the original initial section. -/
@[reassoc] theorem initialGlobalSecondSection_conic :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫
      initialGlobalConic hπ data D j hj hstart hk =
        initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialGlobalConic, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp, initialGlobalSecondSection, fullSecondIncidencePoint_conic]
  rfl

/-- The entire second parameter retains the original initial node at its origin. -/
@[reassoc] theorem initialGlobalConicSecondParameter_origin :
    o ≫ initialGlobalConicSecondParameter hπ data D j hj hstart hk =
      initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialGlobalConicSecondParameter, conicSecondParameterIso_origin_assoc,
    initialGlobalSecondSection_conic]

/-- The complete second initial parameter is over the original residue field. -/
@[reassoc] theorem initialGlobalConicSecondParameter_structure :
    initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫ pullback.fst q f = b := by
  rw [initialGlobalConicSecondParameter]
  simp only [Category.assoc, initialGlobalConic_structure]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c))]
  exact terminalComponent_algebra_structure (conicSecondParameterEquiv a c ha).symm.toAlgHom

/-- The two actual parameter maps cover every point of the retained conic. -/
theorem initialGlobalConicParameters_cover :
    Set.range (initialGlobalConicFirstParameter hπ data D j hj hstart hk) ∪
      Set.range (initialGlobalConicSecondParameter hπ data D j hj hstart hk) =
        Set.range (initialGlobalConic hπ data D j hj hstart hk) := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨conicFirstOpenImmersion a c ((conicFirstParameterIso a c ha).inv p), rfl⟩
    · exact ⟨conicSecondOpenImmersion a c ((conicSecondParameterIso a c ha).inv p), rfl⟩
  · rintro ⟨p, rfl⟩
    rcases conicOpenImmersions_cover a c ha p with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨s, hs⟩ := (conicFirstParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inl ⟨s, congrArg (fun t => initialGlobalConic hπ data D j hj hstart hk
        (conicFirstOpenImmersion a c t)) hs⟩
    · obtain ⟨s, hs⟩ := (conicSecondParameterIso a c ha).inv.homeomorph.surjective t
      exact Or.inr ⟨s, congrArg (fun t => initialGlobalConic hπ data D j hj hstart hk
        (conicSecondOpenImmersion a c t)) hs⟩

end FLT.Mazur.WeierstrassDividedDepth
