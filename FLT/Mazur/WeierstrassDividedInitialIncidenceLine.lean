/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalSections
public import FLT.Mazur.WeierstrassDividedInitialConicParameters
public import FLT.Mazur.WeierstrassModificationXIncidenceLineSections

/-!
# The full initial incidence line in every retained global fiber

This is the affine part of the exterior component, with both original
initial nodes, its coefficient structure, and exact coverage of the initial
chart together with the already constructed full conic parameters.
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
/-- The full initial incidence line, including both exterior node markings. -/
def initialGlobalIncidenceLine := fiberIncidenceImmersion a c ≫ g

instance initialGlobalIncidenceLine_mono :
    Mono (initialGlobalIncidenceLine hπ data D j hj hstart hk) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The complete exterior affine parameter is over the original residue field. -/
@[reassoc] theorem initialGlobalIncidenceLine_structure :
    initialGlobalIncidenceLine hπ data D j hj hstart hk ≫ pullback.fst q f =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
  rw [initialGlobalIncidenceLine, Category.assoc, initialGlobalResidueFiberChart_structure]
  exact terminalComponent_algebra_structure (fiberIncidenceMap a c)

/-- Slope zero on the full incidence line is the first original initial node. -/
@[reassoc] theorem initialGlobalIncidenceLine_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      initialGlobalIncidenceLine hπ data D j hj hstart hk =
        initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialGlobalIncidenceLine, incidenceLineFirstSection_spec_assoc a c ha]
  rfl

/-- Slope minus the tangent coefficient is the second original initial node. -/
@[reassoc] theorem initialGlobalIncidenceLine_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫
      initialGlobalIncidenceLine hπ data D j hj hstart hk =
        initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialGlobalIncidenceLine, incidenceLineSecondSection_spec_assoc a c ha]
  rfl

/-- The complete incidence line and conic exhaust the actual initial chart. -/
theorem initialGlobalIncidenceConic_cover :
    Set.range (initialGlobalIncidenceLine hπ data D j hj hstart hk) ∪
      Set.range (initialGlobalConic hπ data D j hj hstart hk) =
        Set.range (globalInitialTensorChart hπ data K j hj) := by
  let E := residueFiberIso D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨E.hom (fiberIncidenceImmersion a c v), rfl⟩
    · exact ⟨E.hom (fiberConicImmersion a c v), rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, rfl⟩ := E.hom.homeomorph.surjective v
    rcases fiber_incidence_conic_cover a c w with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr ⟨t, rfl⟩

/-- The exterior affine line and two entire conic parameters cover the original initial chart. -/
theorem initialGlobalIncidenceParameters_cover :
    Set.range (initialGlobalIncidenceLine hπ data D j hj hstart hk) ∪
      (Set.range (initialGlobalConicFirstParameter hπ data D j hj hstart hk) ∪
        Set.range (initialGlobalConicSecondParameter hπ data D j hj hstart hk)) =
          Set.range (globalInitialTensorChart hπ data K j hj) := by
  rw [initialGlobalConicParameters_cover, initialGlobalIncidenceConic_cover]

end FLT.Mazur.WeierstrassDividedDepth
