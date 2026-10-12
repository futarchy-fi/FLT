/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertComplementAffinePullback

/-!
# The matching original Hilbert and Grassmannian chart square is cartesian

Affine-test reverse factorization globalizes through the actual Hilbert open
immersion. The resulting lift recovers both projections on arbitrary schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
  {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)
  (hm : Function.Injective m) (e : HilbertComplementMonomials I d m ≃ κ)
local notation "w" => (fun a ↦ MvPolynomial.monomial (Subtype.val (m a)) (1 : R))
local notation "c" => hilbertReindexedAmbient R I d m hm e
local notation "C" => ChartRing R I d w
local notation "j" => ambientGrassmannianChart R
  (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d c
variable {X : Scheme.{u}} (f : X ⟶ polynomialHilbertScheme R I d)
  (g : X ⟶ splitChartScheme R κ d)
  (h : f ≫ hilbertGrassmannianMap R I d b hκ =
    g ≫ ambientGrassmannianChart R
      (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d
        (hilbertReindexedAmbient R I d m hm e))

include hm e g h in
/-- The full compatible scheme test lands in the original Hilbert chart open. -/
theorem hilbertComplement_schemeRange :
    Set.range f ⊆ Set.range (polynomialHilbertChartι R I d w) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := X.affineOpenCover.covers x
  let i := X.affineOpenCover.idx x
  let S := X.affineOpenCover.X i
  let _ := polynomialCoverAlgebra R (f ≫ polynomialHilbertStructure R I d) i
  have hf : (X.affineOpenCover.f i ≫ f) ≫ polynomialHilbertStructure R I d =
      Spec.algebraMap R S := by
    simpa only [Category.assoc] using
      polynomialCoverAlgebra_over R (f ≫ polynomialHilbertStructure R I d) i
  obtain ⟨k, hk, _⟩ := hilbertComplement_affineLift R I d m b hκ hm e S
    (X.affineOpenCover.f i ≫ f) hf (X.affineOpenCover.f i ≫ g)
    (by simpa only [Category.assoc] using congrArg (X.affineOpenCover.f i ≫ ·) h)
  refine ⟨k y, ?_⟩
  change (k ≫ polynomialHilbertChartι R I d w) y = _
  rw [hk.1]
  change f (X.affineOpenCover.f i y) = f x
  rw [show X.affineOpenCover.f i y = x from hy]

/-- Construct the reverse factorization on an arbitrary compatible scheme test. -/
def hilbertComplementSchemeLift : X ⟶ Spec (.of C) :=
  IsOpenImmersion.lift (polynomialHilbertChartι R I d w) f
    (hilbertComplement_schemeRange R I d m b hκ hm e f g h)

/-- The constructed lift recovers the original Hilbert parameter. -/
theorem hilbertComplementSchemeLift_ι :
    hilbertComplementSchemeLift R I d m b hκ hm e f g h ≫
      polynomialHilbertChartι R I d w = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The same lift recovers the specified Grassmannian chart parameter. -/
theorem hilbertComplementSchemeLift_map :
    hilbertComplementSchemeLift R I d m b hκ hm e f g h ≫
      hilbertReindexedChartMap R I d m e = g := by
  apply (cancel_mono j).mp
  rw [Category.assoc, hilbertReindexedChartMap_global R I d m b hκ hm e,
    ← Category.assoc, hilbertComplementSchemeLift_ι, h]

include h hm in
/-- The unique compatible lift exists on all original scheme tests. -/
theorem hilbertComplement_schemeLift_unique :
    ∃! k : X ⟶ Spec (.of C), k ≫ polynomialHilbertChartι R I d w = f ∧
      k ≫ hilbertReindexedChartMap R I d m e = g := by
  refine ⟨hilbertComplementSchemeLift R I d m b hκ hm e f g h,
    ⟨hilbertComplementSchemeLift_ι R I d m b hκ hm e f g h,
      hilbertComplementSchemeLift_map R I d m b hκ hm e f g h⟩, ?_⟩
  intro k hk
  apply (cancel_mono (polynomialHilbertChartι R I d w)).mp
  rw [hk.1, hilbertComplementSchemeLift_ι]

/-- The original closed Hilbert chart is the full pullback of its Grassmannian chart. -/
theorem hilbertComplement_isPullback :
    IsPullback (polynomialHilbertChartι R I d w) (hilbertReindexedChartMap R I d m e)
      (hilbertGrassmannianMap R I d b hκ) j := by
  let lift (z : PullbackCone (hilbertGrassmannianMap R I d b hκ) j) :=
    hilbertComplement_schemeLift_unique R I d m b hκ hm e z.fst z.snd z.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (hilbertReindexedChartMap_global R I d m b hκ hm e).symm
    (fun z ↦ (lift z).choose) (fun z ↦ (lift z).choose_spec.1.1)
    (fun z ↦ (lift z).choose_spec.1.2)
    (fun z k hk hg ↦ (lift z).choose_spec.2 k ⟨hk, hg⟩))

/-- The original Hilbert chart is exactly the full inverse-image locus of its target chart. -/
theorem hilbertComplement_chart_preimage :
    Set.range (polynomialHilbertChartι R I d w) =
      (hilbertGrassmannianMap R I d b hκ) ⁻¹' Set.range j := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨hilbertReindexedChartMap R I d m e z, congrArg (fun k ↦ k z)
      (hilbertReindexedChartMap_global R I d m b hκ hm e)⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (hilbertComplement_isPullback R I d m b hκ hm e) x y hy.symm
    exact ⟨z, hz⟩

end FLT.Mazur.HilbertChart
