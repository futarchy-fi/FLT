/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryEtaleIdeals
public import FLT.Mazur.EnvelopeBoundaryTestLift
public import FLT.Mazur.InvariantBoundaryPullback

/-!
# Whole original Hilbert tests on the closed boundary

The finite equations define an actual closed scheme over the unchanged
coefficient base. Their exact vanishing constructs unique relative lifts,
retaining the whole Hilbert parameter and original Picard section. Equal
original Picard classes give equal equation ideals on all affine tests;
vanishing is consequently independent of the selected original lift.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryEquationLift boundaryIdealSheaf originalInteriorEquations
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "I" => boundaryIdealSheaf π O
local notation "j" => Scheme.IdealSheafData.subschemeι I

/-- The actual closed boundary retains its original coefficient scheme. -/
def originalBoundarySource : Over (Spec (.of R)) := Over.mk (j ≫ A.hom)

/-- The original closed source inclusion. -/
def originalBoundarySourceMap : originalBoundarySource f hL d V c k ⟶ A := Over.homMk j

local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)

/-- The full original endpoints induce an actual comparison of closed boundary schemes. -/
def originalBoundaryRelationIso : pullback p j ≅ pullback q j := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact boundaryPullbackIso π O p q (fullEnvelopeInterior_invariant f hL d V c k)

/-- The comparison preserves the whole original relation morphism. -/
@[reassoc]
theorem originalBoundaryRelationIso_fst :
    (originalBoundaryRelationIso f hL d V c k).hom ≫ pullback.fst q j =
      pullback.fst p j := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact boundaryPullbackIso_fst π O p q (fullEnvelopeInterior_invariant f hL d V c k)

variable {T : Over (Spec (.of R))} [IsAffine T.left] (b : T ⟶ A)

/-- Equal original Picard classes give exactly equal pulled-back equation ideals. -/
theorem originalBoundaryEquations_class_eq (b' : T ⟶ A)
    (hc : (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) =
      (relativeFppfSheaf f).obj.map b'.op (sectionAt f hL d V c k)) :
    Ideal.span (b.left.appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) =
    Ideal.span (b'.left.appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) := by
  obtain ⟨z, hz, _⟩ := lift f hL d V c k b b' hc
  have hp : z.left ≫ (fst f hL d V c k).left = b.left := congrArg Over.Hom.left hz.1
  have hq : z.left ≫ (snd f hL d V c k).left = b'.left := congrArg Over.Hom.left hz.2
  simpa only [hp, hq] using originalEquations_relation_span_eq f hL d V c k z.left

variable (h : Ideal.span (b.left.appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) = ⊥)
local notation "i" => originalBoundarySourceMap f hL d V c k

/-- Exact vanishing constructs a lift of the whole original test over the same base. -/
def originalBoundaryEquationLift : T ⟶ originalBoundarySource f hL d V c k := by
  let z : T.left ⟶ (I).subscheme := boundaryEquationLift (T := T.left) π O
    (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))
    (originalInteriorEquations_span f hL d V c k) b.left h
  refine Over.homMk z ?_
  change z ≫ j ≫ A.hom = T.hom
  rw [← Category.assoc, boundaryEquationLift_comp]
  exact b.w

/-- The lift retains the original affine parameter map. -/
@[reassoc]
theorem originalBoundaryEquationLift_comp :
    originalBoundaryEquationLift f hL d V c k b h ≫ i = b := by
  apply Over.OverMorphism.ext
  exact boundaryEquationLift_comp π O
    (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))
    (originalInteriorEquations_span f hL d V c k) b.left h

/-- The entire original Hilbert parameter is retained, including nilpotents. -/
@[reassoc]
theorem originalBoundaryEquationLift_chart :
    originalBoundaryEquationLift f hL d V c k b h ≫ (i ≫ k) = b ≫ k := by
  rw [originalBoundaryEquationLift_comp_assoc]

/-- The original Picard section is retained on the entire test. -/
theorem originalBoundaryEquationLift_section :
    (relativeFppfSheaf f).obj.map (originalBoundaryEquationLift f hL d V c k b h).op
      ((relativeFppfSheaf f).obj.map (i).op (sectionAt f hL d V c k)) =
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    originalBoundaryEquationLift_comp]

/-- Relative closed lifts are unique as whole scheme morphisms. -/
theorem originalBoundaryEquationLift_unique (z : T ⟶ originalBoundarySource f hL d V c k)
    (hz : z ≫ i = b) : z = originalBoundaryEquationLift f hL d V c k b h := by
  apply Over.OverMorphism.ext
  exact boundaryEquationLift_unique π O
    (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))
    (originalInteriorEquations_span f hL d V c k) b.left h z.left (congrArg Over.Hom.left hz)

end FLT.Mazur.HilbertChart.AffineRestriction
