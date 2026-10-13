/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertCompositionFiniteBranches
public import FLT.Mazur.EtaleFiniteBranchDiagramAtlas

/-!
# Original coefficient laws on the constructed branch composition atlas

Every member lifts both inputs and their composite into actual finite
branches. The middle endpoint and both outer endpoint maps agree as scheme
morphisms; their induced coefficient homomorphisms therefore agree too.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "g" => compositionLeg f hL d V c k
local notation "Z" => EtaleFiniteBranchDiagramAtlas.source p (g 0) Finset.univ g
local notation "a" => EtaleFiniteBranchDiagramAtlas.original p (g 0) Finset.univ g

/-- The actual target branch selected for one of the three original arrows. -/
def compositionBranchIndex (x : (pullback q p).left) (j : Fin 3) : (D).left :=
  (EtaleFiniteBranchDiagramAtlas.lifts p (g 0) Finset.univ g x j (Finset.mem_univ j)).choose

/-- The actual etale lift of an input or the composite into its selected finite branch. -/
def compositionBranchLift (x : (pullback q p).left) (j : Fin 3) :
    Z x ⟶ EtaleFiniteBranchAtlas.source p (compositionBranchIndex f hL d V c k x j) :=
  (EtaleFiniteBranchDiagramAtlas.lifts p (g 0) Finset.univ g x j
    (Finset.mem_univ j)).choose_spec.choose

instance compositionBranchLift_etale (x : (pullback q p).left) (j : Fin 3) :
    Etale (compositionBranchLift f hL d V c k x j).left :=
  (EtaleFiniteBranchDiagramAtlas.lifts p (g 0) Finset.univ g x j
    (Finset.mem_univ j)).choose_spec.choose_spec.1

/-- The lift recovers the complete original arrow as a relative scheme morphism. -/
@[reassoc]
theorem compositionBranchLift_original (x : (pullback q p).left) (j : Fin 3) :
    compositionBranchLift f hL d V c k x j ≫
      EtaleFiniteBranchAtlas.original p (compositionBranchIndex f hL d V c k x j) =
        a x ≫ g j :=
  (EtaleFiniteBranchDiagramAtlas.lifts p (g 0) Finset.univ g x j
    (Finset.mem_univ j)).choose_spec.choose_spec.2.symm

/-- The branch diagram really covers the full original composition scheme on its relative site. -/
theorem compositionBranch_covering : Sieve.ofArrows Z a ∈
    (Scheme.fppfTopology.over (Spec (.of R))) (pullback q p) :=
  EtaleFiniteBranchDiagramAtlas.covering p (g 0) Finset.univ g

/-- Evaluate the selected branch lift in the original full relation. -/
def compositionBranchArrow (x : (pullback q p).left) (j : Fin 3) : Z x ⟶ D :=
  compositionBranchLift f hL d V c k x j ≫
    EtaleFiniteBranchAtlas.original p (compositionBranchIndex f hL d V c k x j)

local notation "l" => compositionBranchArrow f hL d V c k

/-- The composite and first input have exactly the same original first endpoint. -/
theorem compositionBranch_source (x : (pullback q p).left) :
    l x 2 ≫ p = l x 0 ≫ p := by
  simp only [compositionBranchArrow, compositionBranchLift_original_assoc,
    compositionLeg_two, compositionLeg_zero, Category.assoc, fullComposition_fst]

/-- The two lifted input branches have exactly the same original middle endpoint. -/
theorem compositionBranch_middle (x : (pullback q p).left) :
    l x 0 ≫ q = l x 1 ≫ p := by
  simp only [compositionBranchArrow, compositionBranchLift_original_assoc,
    compositionLeg_zero, compositionLeg_one, Category.assoc, pullback.condition]

/-- The composite and second input have exactly the same original second endpoint. -/
theorem compositionBranch_target (x : (pullback q p).left) :
    l x 2 ≫ q = l x 1 ≫ q := by
  simp only [compositionBranchArrow, compositionBranchLift_original_assoc,
    compositionLeg_two, compositionLeg_one, Category.assoc, fullComposition_snd]

/-- The first coefficient homomorphisms agree on the constructed common branch source. -/
theorem compositionBranch_source_coefficients (x : (pullback q p).left) :
    (l x 2 ≫ p).left.appTop = (l x 0 ≫ p).left.appTop :=
  congrArg (fun h ↦ h.left.appTop) (compositionBranch_source f hL d V c k x)

/-- The middle coefficient homomorphisms agree without identifying the two branch targets. -/
theorem compositionBranch_middle_coefficients (x : (pullback q p).left) :
    (l x 0 ≫ q).left.appTop = (l x 1 ≫ p).left.appTop :=
  congrArg (fun h ↦ h.left.appTop) (compositionBranch_middle f hL d V c k x)

/-- The last coefficient homomorphisms agree on the constructed common branch source. -/
theorem compositionBranch_target_coefficients (x : (pullback q p).left) :
    (l x 2 ≫ q).left.appTop = (l x 1 ≫ q).left.appTop :=
  congrArg (fun h ↦ h.left.appTop) (compositionBranch_target f hL d V c k x)

/-- Every leg retains the same original Picard class from the actual coefficient scheme. -/
theorem compositionBranch_original_class (x : (pullback q p).left) (j : Fin 3) :
    (relativeFppfSheaf f).obj.map (l x j ≫ p).op (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map
        (EtaleFiniteBranchDiagramAtlas.projection p (g 0) Finset.univ g x).op
        ((relativeFppfSheaf f).obj.map
          (EtaleFiniteBranchDiagramAtlas.base p (g 0) Finset.univ g x).op
          (sectionAt f hL d V c k)) := by
  have h0 : l x 0 ≫ p =
      EtaleFiniteBranchDiagramAtlas.projection p (g 0) Finset.univ g x ≫
        EtaleFiniteBranchDiagramAtlas.base p (g 0) Finset.univ g x := by
    rw [compositionBranchArrow, compositionBranchLift_original, Category.assoc]
    exact EtaleFiniteBranchDiagramAtlas.condition p (g 0) Finset.univ g x
  have hc := equal_class_natural f hL d V c k (l x 0)
  fin_cases j
  · change (relativeFppfSheaf f).obj.map (l x 0 ≫ p).op _ = _
    rw [h0, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  · change (relativeFppfSheaf f).obj.map (l x 1 ≫ p).op _ = _
    rw [← compositionBranch_middle, ← hc, h0, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]
  · change (relativeFppfSheaf f).obj.map (l x 2 ≫ p).op _ = _
    rw [compositionBranch_source, h0, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]

end FLT.Mazur.HilbertChart.AffineRestriction
