/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitFiniteQuotient
public import FLT.Mazur.CyclicCharacteristicDisjointCartesian

/-!
# The residual topological quotient of the assembled finite quotient

The full orbit map factors continuously through the actual disjoint finite
quotient. The residual map is itself a quotient map and retains every full
comparison orbit, including comparisons across the characteristic charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "Q" => normalizedDisjointQuotient n
local notation "q" => normalizedDisjointQuotientMap n

/-- Every assembled relabeling already lies in the full comparison relation. -/
theorem related_disjoint_relabel (g : RelabelGroup n) (x : U) :
    Related n ((normalizedDisjointAction n g).hom x) x := by
  obtain ⟨b, x, rfl⟩ := (sigmaOpenCover (normalizedLocus n)).exists_eq x
  change Related n ((normalizedDisjointAction n g).hom (normalizedDisjointInclusion n b x))
    (normalizedDisjointInclusion n b x)
  have h := congrArg (fun k ↦ k x) (normalizedDisjointAction_inclusion n b g)
  rw [show (normalizedDisjointAction n g).hom (normalizedDisjointInclusion n b x) =
      normalizedDisjointInclusion n b ((normalizedRelabelAction n b g).hom x) from h]
  exact related_relabel n b g x

/-- The full orbit projection is constant on every fiber of the assembled finite quotient. -/
theorem projection_eq_of_disjoint_quotient_eq (x y : U) (h : q x = q y) :
    projection n x = projection n y := by
  obtain ⟨g, rfl⟩ := (normalizedDisjointQuotientMap_eq_iff_orbit n x y).mp h
  exact ((projection_eq_iff n _ _).mpr (related_disjoint_relabel n g x)).symm

/-- The residual map from the actual finite quotient to the full comparison orbit space. -/
def residualProjection (y : Q) : Orbit n :=
  projection n ((q).surjective y).choose

/-- The residual projection factors the original full orbit projection. -/
theorem residualProjection_apply (x : U) : residualProjection n (q x) = projection n x :=
  projection_eq_of_disjoint_quotient_eq n _ x ((q).surjective (q x)).choose_spec

/-- The factorization is continuous for the actual finite quotient topology. -/
theorem residualProjection_continuous : Continuous (residualProjection n) := by
  apply (normalizedDisjointQuotientMap_isQuotientMap n).continuous_iff.mpr
  have he : residualProjection n ∘ q = projection n := funext (residualProjection_apply n)
  rw [he]
  exact projection_continuous n

/-- Passing to the finite quotient has not lost the full orbit quotient topology. -/
theorem residualProjection_isQuotientMap : IsQuotientMap (residualProjection n) := by
  apply (normalizedDisjointQuotientMap_isQuotientMap n).of_comp_isQuotientMap
  have he : residualProjection n ∘ q = projection n := funext (residualProjection_apply n)
  rw [he]
  exact projection_isQuotientMap n

/-- The residual projection is a continuous map from the actual finite quotient scheme. -/
def residualQuotientMap : (Q).toTopCat ⟶ space n :=
  TopCat.ofHom ⟨residualProjection n, residualProjection_continuous n⟩

/-- The entire original orbit map factors through this residual continuous quotient. -/
theorem normalizedDisjointQuotientMap_residualQuotientMap :
    (q).base ≫ residualQuotientMap n = quotientMap n := by
  ext x
  exact residualProjection_apply n x

/-- On either original quotient component, this is the previously constructed residual map. -/
theorem residualProjection_inclusion (b : Bool) (y : normalizedQuotient n b) :
    residualProjection n (normalizedDisjointQuotientInclusion n b y) =
      finiteProjection n b y := by
  obtain ⟨x, rfl⟩ := (normalizedQuotientMap n b).surjective y
  rw [finiteProjection_apply]
  have he := congrArg (fun k ↦ k x) (normalizedDisjointInclusion_quotientMap n b)
  simp only [Scheme.Hom.comp_apply] at he
  rw [← he]
  exact residualProjection_apply n (normalizedDisjointInclusion n b x)

end FLT.Mazur.CyclicCharacteristicOrbit
