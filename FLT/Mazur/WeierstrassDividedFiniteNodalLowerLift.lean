/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalLowerReindex
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.WeierstrassDividedVerticalRefinement

/-!
# Shallow nodal branch outputs in the chosen entire finite model

At any admissible shallow nodal depth, insert the constructed
output into the entire finite model. Its derivative localization maps to the full
smooth locus, retaining the original tangent contraction and coefficient point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m) (hdepth : 2 * k ≤ m)
  (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hj : m - 2 * k ≤ n) (d : Data W π k)
  (a2 : R) (h2 : W.a₂ = π ^ (m - 2 * k) * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "e" => data ⟨m - 2 * k, Nat.lt_succ_of_le hj⟩
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "res" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "raw" => nodalLowerReindexedLift
  D d hdepth hm e (Nat.zero_add _) a2 h2 a c
local notation "out" => nodalLowerReindexedOutput
  D d hdepth hm e (Nat.zero_add _) a2 h2 a c
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "U" => (base).smoothLocus

/-- Insert the genuine shallow output into the chosen entire finite model. -/
def finiteNodalLowerLift :
    Spec (.of B) ⟶ finiteGlobalModel hπ (start := 0) data (m - 2 * k) hj :=
  raw ≫ finiteSecantDividedChart hπ (start := 0) data (m - 2 * k) hj

local notation "F" => finiteNodalLowerLift D hdepth hm data hj d a2 h2 a c

/-- The full deeper output retains the actual original tangent sum. -/
@[reassoc] theorem finiteNodalLowerLift_contraction :
    F ≫ finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [finiteNodalLowerLift, Category.assoc, finiteSecantDividedChart_contraction]
  exact nodalLowerReindexedLift_contraction ..

/-- The entire deeper output retains the source coefficient point. -/
@[reassoc] theorem finiteNodalLowerLift_structure :
    F ≫ base = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteNodalLowerLift, Category.assoc, finiteSecantDividedChart_structure]
  exact nodalLowerReindexedLift_structure ..

/-- The pulled-back vertical derivative at the actual final depth. -/
def finiteNodalLowerDerivative : B :=
  out (verticalDerivative W (π ^ (0 + (m - 2 * k))) (e).b3 (e).b4 (e).b6)

local notation "δ" => finiteNodalLowerDerivative D hdepth hm data hj d a2 h2 a c
local notation "i" => PrincipalAffineRefinement.inclusion δ
variable [IsNoetherianRing R]

/-- The derivative neighborhood lands in the chosen finite model's full smooth locus. -/
theorem finiteNodalLowerRefinement_range_smooth : Set.range (i ≫ F) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq
    (finiteSecantDividedChart hπ (start := 0) data (m - 2 * k) hj) base
  simp only [finiteSecantDividedChart_structure] at h
  apply h.ge
  exact dividedVerticalRefinement_range_smooth W (π ^ (0 + (m - 2 * k)))
    (e).b3 (e).b4 (e).b6 out ⟨z, rfl⟩

/-- The constructed deeper output on its explicit smooth principal neighborhood. -/
def finiteNodalLowerSmoothLift : Spec (.of (Localization.Away δ)) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (i ≫ F) (by
    rw [Scheme.Opens.range_ι]
    exact finiteNodalLowerRefinement_range_smooth D hdepth hm data hj d a2 h2 a c)

/-- Including the smooth output recovers the entire finite-model output. -/
@[reassoc] theorem finiteNodalLowerSmoothLift_inclusion :
    finiteNodalLowerSmoothLift D hdepth hm data hj d a2 h2 a c ≫ (U).ι = i ≫ F :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth output retains exactly the original tangent contraction. -/
@[reassoc] theorem finiteNodalLowerSmoothLift_contraction :
    finiteNodalLowerSmoothLift D hdepth hm data hj d a2 h2 a c ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      i ≫ Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [finiteNodalLowerSmoothLift_inclusion_assoc, finiteNodalLowerLift_contraction]

/-- The entire shallow nodal fiber maps to the finite model's smooth locus. -/
theorem finiteNodalLower_nodal_smooth
    (hlo : 2 * k < m) (hhi : m < 3 * k) (ha2 : a2 ∈ IsLocalRing.maximalIdeal R)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) : F p ∈ U := by
  have hmem := nodalLowerReindexedOutput_nodal_mem D d hdepth hm e (Nat.zero_add _)
    a2 h2 a c hlo hhi ha2 p hp
  have hrange : p ∈ Set.range i := by
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hmem
  obtain ⟨z, hz⟩ := hrange
  exact finiteNodalLowerRefinement_range_smooth D hdepth hm data hj d a2 h2 a c
    ⟨z, congrArg F hz⟩

end FLT.Mazur.WeierstrassDividedDepth
