/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatBoundaryCoordinateEquations
public import FLT.Mazur.FlatScalarSchemeBaseChange
public import FLT.Mazur.OriginalBoundaryTensorLift

/-!
# Full geometric coordinates for original boundary tensor lifts

Both endpoint arrows and the full boundary restriction are base changed over
the actual original invariant ring. Their coefficient comparisons and squares
are constructed, rather than supplied as hypotheses about branch coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatAlgebraEqualizer
open FlatScalarSchemeBaseChange FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} (p q : D ⟶ A) (J : A.IdealSheafData)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]

/-- The first endpoint on the full geometric flat branch. -/
def originalBranchFirst : baseChange R S D ⟶ baseChange R S A :=
  FlatScalarSchemeBaseChange.map p (first p.appTop.hom q.appTop.hom) rfl

/-- The independently constructed second endpoint on the same full branch. -/
def originalBranchSecond : baseChange R S D ⟶ baseChange R S A :=
  FlatScalarSchemeBaseChange.map q (second p.appTop.hom q.appTop.hom) rfl

/-- Restriction to the base change of the entire original boundary. -/
def originalBranchBoundary : baseChange R S J.subscheme ⟶ baseChange R S A :=
  FlatScalarSchemeBaseChange.map J.subschemeι (originalBoundaryMap J) rfl

variable [Module.Flat (invariants p.appTop.hom q.appTop.hom) S]
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D]
  [CompactSpace J.subscheme] [QuasiSeparatedSpace J.subscheme]

/-- Actual full branch functions and full tensor numerators have exactly the same equations. -/
theorem originalBoundary_tensor_lift_iff_geometric (t : Γ(J.subscheme, ⊤)) :
    (∃ a : S ⊗[R] Γ(A, ⊤),
      tensorMap S (first p.appTop.hom q.appTop.hom) a =
        tensorMap S (second p.appTop.hom q.appTop.hom) a ∧
      tensorMap S (originalBoundaryMap J) a = 1 ⊗ₜ[R] t) ↔
    ∃ a : Γ(baseChange R S A, ⊤),
      (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a ∧
      (originalBranchBoundary p q J S).appTop a = (source R S J.subscheme).appTop t := by
  let ea := sectionsEquiv (square R S A)
  let ec := sectionsEquiv (square R S D)
  let eb := sectionsEquiv (square R S J.subscheme)
  have hp (x : S ⊗[R] Γ(A, ⊤)) :
      ec (tensorMap S (first p.appTop.hom q.appTop.hom) x) =
        (originalBranchFirst p q S).appTop (ea x) := map_sectionsEquiv p _ rfl x
  have hq (x : S ⊗[R] Γ(A, ⊤)) :
      ec (tensorMap S (second p.appTop.hom q.appTop.hom) x) =
        (originalBranchSecond p q S).appTop (ea x) := map_sectionsEquiv q _ rfl x
  have hb (x : S ⊗[R] Γ(A, ⊤)) : eb (tensorMap S (originalBoundaryMap J) x) =
      (originalBranchBoundary p q J S).appTop (ea x) :=
    map_sectionsEquiv J.subschemeι _ rfl x
  have ht : eb (1 ⊗ₜ[R] t) = (source R S J.subscheme).appTop t :=
    sectionsEquiv_right (square R S J.subscheme) t
  exact FlatBoundaryCoordinateEquations.lift_iff _ _ _ ea ec eb
    (originalBranchFirst p q S).appTop.hom (originalBranchSecond p q S).appTop.hom
    (originalBranchBoundary p q J S).appTop.hom hp hq hb t _ ht

/-- A geometric branch lift constructs a nonvanishing original full-boundary multiplier. -/
theorem exists_originalBoundaryLift_multiplier_of_geometric
    (P : Ideal S) (hP : P ≠ ⊤) (t : Γ(J.subscheme, ⊤))
    (a : Γ(baseChange R S A, ⊤))
    (he : (originalBranchFirst p q S).appTop a = (originalBranchSecond p q S).appTop a)
    (hb : (originalBranchBoundary p q J S).appTop a =
      (source R S J.subscheme).appTop t) :
    ∃ r : R, algebraMap R S r ∉ P ∧ r ∈ originalBoundaryLiftIdeal J t := by
  obtain ⟨x, hx, hb⟩ :=
    (originalBoundary_tensor_lift_iff_geometric p q J S t).mpr ⟨a, he, hb⟩
  apply exists_originalBoundaryLift_multiplier_of_tensor J S P t 1
    (fun h ↦ hP (P.eq_top_iff_one.mpr h)) x hx
  simpa only [map_one, one_mul] using hb

end FLT.Mazur.EquivalenceRelationOrderedFrames
