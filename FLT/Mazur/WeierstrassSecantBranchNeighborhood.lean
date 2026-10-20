/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearBranchOverlap
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Common secant neighborhoods retaining smooth branch outputs

Pull back a branch open after restricting its output to a specified open.
The resulting neighborhood is open in the original source, retains every
input morphism, and has an actual output in the prescribed open subscheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The sheared branch overlap is an actual open of its original input algebra. -/
def dividedShearBranchInclusion {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
    (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    Spec (.of (DividedShearBranchOverlap W s b3 b4 b6 r a c)) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S _))

instance dividedShearBranchInclusion_open {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
    (a c : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    IsOpenImmersion (dividedShearBranchInclusion W s b3 b4 b6 r a c) :=
  IsOpenImmersion.of_isLocalization
    (dividedTangentDenominator W s b3 b4 b6 a c *
      (dividedTangentDenominator (WeierstrassDividedDepth.rootShearCurve W r)
        s b3 (b4 - r * b3) b6 (branchShearInput W s b3 b4 b6 r a)
        (branchShearInput W s b3 b4 b6 r c) *
      dividedTangentBranchFactor (WeierstrassDividedDepth.rootShearCurve W r)
        s b3 (b4 - r * b3) b6 (branchShearInput W s b3 b4 b6 r a)))

variable {X S B M : Scheme.{u}} (t : X ⟶ S) (j : B ⟶ S) [IsOpenImmersion j]
  (f : B ⟶ M) (U : M.Opens)
local notation "V" => f ⁻¹ᵁ U
local notation "b" => (V).ι ≫ j

/-- A common neighborhood in the original source with output in the chosen open. -/
def secantBranchNeighborhood : Scheme := pullback t b

/-- The neighborhood inclusion into the unchanged source. -/
def secantBranchNeighborhoodInclusion : secantBranchNeighborhood t j f U ⟶ X :=
  pullback.fst t b

instance secantBranchNeighborhoodInclusion_open :
    IsOpenImmersion (secantBranchNeighborhoodInclusion t j f U) := by
  unfold secantBranchNeighborhoodInclusion
  infer_instance

/-- The actual comparison with the original branch source. -/
def secantBranchNeighborhoodBranch : secantBranchNeighborhood t j f U ⟶ B :=
  pullback.snd t b ≫ (V).ι

/-- The constructed output lands in the chosen open everywhere on the neighborhood. -/
def secantBranchNeighborhoodOutput : secantBranchNeighborhood t j f U ⟶ U.toScheme :=
  pullback.snd t b ≫ (f ∣_ U)

omit [IsOpenImmersion j] in
/-- Both source maps agree, including on nonreduced test schemes. -/
@[reassoc] theorem secantBranchNeighborhood_source :
    secantBranchNeighborhoodBranch t j f U ≫ j =
      secantBranchNeighborhoodInclusion t j f U ≫ t := by
  exact (Category.assoc _ _ _).trans (pullback.condition.symm)

omit [IsOpenImmersion j] in
/-- The output is the restriction of the entire actual branch output. -/
@[reassoc] theorem secantBranchNeighborhoodOutput_inclusion :
    secantBranchNeighborhoodOutput t j f U ≫ U.ι =
      secantBranchNeighborhoodBranch t j f U ≫ f := by
  simp only [secantBranchNeighborhoodOutput, secantBranchNeighborhoodBranch,
    Category.assoc, morphismRestrict_ι]

omit [IsOpenImmersion j] in
/-- Every original input map is retained by the constructed common neighborhood. -/
theorem secantBranchNeighborhood_input {C : Scheme} (a : S ⟶ C) :
    secantBranchNeighborhoodBranch t j f U ≫ j ≫ a =
      secantBranchNeighborhoodInclusion t j f U ≫ t ≫ a :=
  secantBranchNeighborhood_source_assoc t j f U a

/-- A branch point with smooth output gives a neighborhood of the original source point. -/
theorem secantBranchNeighborhood_covers (p : X) (q : B)
    (hq : j q = t p) (hf : f q ∈ U) :
    p ∈ Set.range (secantBranchNeighborhoodInclusion t j f U) := by
  change p ∈ Set.range (pullback.fst t b)
  rw [IsOpenImmersion.range_pullbackFst]
  exact ⟨⟨q, hf⟩, hq⟩

end FLT.Mazur.WeierstrassDilatation
