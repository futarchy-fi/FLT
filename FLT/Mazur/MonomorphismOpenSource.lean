/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFppfImage
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# The maximal open source of a monomorphism

The inverse on the maximal open image is itself an open immersion into the
original source. This constructs actual open charts, even when the original
map is not an immersion. A source point is retained exactly when it admits
an open source neighborhood mapping openly to the original target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.MonomorphismOpenImage
variable {D K : Scheme.{u}} (m : D ⟶ K) [Mono m]

/-- The constructed inverse is an open immersion into the entire original source. -/
instance lift_isOpenImmersion : IsOpenImmersion (lift m) := by
  have he : lift m = (inverseImageIso m).inv ≫ pullback.fst m (locus m).ι := by
    exact (pullback.lift_fst _ _ _).symm
  rw [he]
  infer_instance

/-- The actual source open retains its original scheme structure. -/
def sourceOpen : D.Opens := m ⁻¹ᵁ locus m

/-- The inverse reaches precisely the full inverse image of the open target locus. -/
theorem range_lift : Set.range (lift m) = (sourceOpen m : Set D) := by
  ext d
  constructor
  · rintro ⟨x, rfl⟩
    change m (lift m x) ∈ locus m
    rw [← Scheme.Hom.comp_apply, lift_comp]
    exact x.property
  · intro hd
    refine ⟨⟨m d, hd⟩, ?_⟩
    apply m.injective
    exact congrArg (fun g ↦ g ⟨m d, hd⟩) (lift_comp m)

/-- The inverse identifies the open image with an actual open of the original source. -/
def sourceOpenIso : (locus m).toScheme ≅ (sourceOpen m).toScheme :=
  IsOpenImmersion.isoOfRangeEq (lift m) (sourceOpen m).ι (by
    rw [Scheme.Opens.range_ι, range_lift])

@[reassoc]
theorem sourceOpenIso_hom_ι : (sourceOpenIso m).hom ≫ (sourceOpen m).ι = lift m :=
  IsOpenImmersion.lift_fac _ _ _

/-- Every open source chart that maps openly into the target is retained. -/
theorem source_chart_le {Y : Scheme.{u}} (a : Y ⟶ D) [IsOpenImmersion (a ≫ m)] :
    Set.range a ⊆ (sourceOpen m : Set D) := by
  rintro _ ⟨y, rfl⟩
  exact mem_locus_of_fppf_lift m (a ≫ m) a rfl y

/-- Exact local criterion, with no reduced-test or global flatness assumption. -/
theorem mem_sourceOpen_iff (d : D) : d ∈ sourceOpen m ↔
    ∃ (Y : Scheme.{u}) (a : Y ⟶ D) (y : Y),
      IsOpenImmersion a ∧ IsOpenImmersion (a ≫ m) ∧ a y = d := by
  constructor
  · intro hd
    have hr : d ∈ Set.range (lift m) := by
      rw [range_lift]
      exact hd
    obtain ⟨y, hy⟩ := hr
    refine ⟨(locus m).toScheme, lift m, y, inferInstance, ?_, hy⟩
    rw [lift_comp]
    infer_instance
  · rintro ⟨Y, a, y, _, ha, rfl⟩
    let _ := ha
    exact source_chart_le m a ⟨y, rfl⟩

/-- A globally flat finitely presented comparison retains every original source point. -/
theorem sourceOpen_eq_top [Flat m] [LocallyOfFinitePresentation m] : sourceOpen m = ⊤ := by
  apply top_le_iff.mp
  intro d _
  exact mem_locus_of_fppf_lift m m (𝟙 D) (Category.id_comp m) d

end FLT.Mazur.MonomorphismOpenImage
