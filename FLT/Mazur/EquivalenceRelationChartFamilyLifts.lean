/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartFamilyCorrections
public import FLT.Mazur.EquivalenceRelationMixedChartLiftDifference

/-!
# The actual simultaneous correction obstruction of an original open section

Every original equalized boundary section has a family of invariant affine
chart lifts. Their discrepancies lie in the exact original mixed boundary
kernels. Their single simultaneous obstruction is independent of all choices;
its vanishing, which is not asserted here, gives compatible ambient lifts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
open InvariantBoundary SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary MixedFrames.relation jointBoundaryTarget
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (EquivalenceRelationNormalizedFrames.action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ
    U a = U a)
  (i : B ⟶ A) [IsClosedImmersion i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
  (hUE : ∀ a, InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U a ≤
    endpoint (Fin (n a)) (o a) i ⁻¹ᵁ E)
  (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)

/-- The actual original open section on every full chart boundary. -/
def boundaryCoefficient :
    ∀ a, Γ((InvariantBoundary.inclusion (Fin (n a)) (o a) i ⁻¹ᵁ U a).toScheme, ⊤) :=
  fun a ↦ ((endpoint (Fin (n a)) (o a) i).resLE E _ (hUE a)).appTop t

include hr hs ht in
/-- Invariant lifts can be chosen simultaneously for every independently selected affine chart. -/
theorem exists_lift_family (hUa : ∀ a, IsAffineOpen (U a)) :
    ∃ v : Sections e n o U hU, restriction e n o U hU i v =
      boundaryCoefficient n o U i E hUE t := by
  have h : ∀ a, ∃ v : invariantCoordinates
      (restrictedAction (EquivalenceRelationNormalizedFrames.action e (Fin (n a)) (o a))
        (U a) (hU a)),
      (InvariantBoundary.inclusion (Fin (n a)) (o a) i ∣_ U a).appTop v.val =
        boundaryCoefficient n o U i E hUE t a := by
    intro a
    obtain ⟨v, hv⟩ := domainInvariantCoefficient_lift e (Fin (n a)) (o a) i z r s hr hs
      E hE (U a) (hU a) (hUE a) t ht (hUa a)
    exact ⟨v, congrArg Subtype.val hv⟩
  choose v hv using h
  exact ⟨v, funext hv⟩

variable (hUa : ∀ a, IsAffineOpen (U a))

/-- A chosen actual lift family, without an assumption of compatibility. -/
def liftFamily : Sections e n o U hU :=
  Classical.choose (exists_lift_family e n o U hU i z r s hr hs E hE hUE t ht hUa)

/-- The chosen family restricts to the original section on every entire chart boundary. -/
theorem liftFamily_restriction :
    restriction e n o U hU i (liftFamily e n o U hU i z r s hr hs E hE hUE t ht hUa) =
      boundaryCoefficient n o U i E hUE t :=
  Classical.choose_spec (exists_lift_family e n o U hU i z r s hr hs E hE hUE t ht hUa)

/-- The original open section's simultaneous obstruction, using all original mixed relations. -/
def originalObstruction :=
  defect e n o U hU i (liftFamily e n o U hU i z r s hr hs E hE hUE t ht hUa)

/-- Any actual lift family computes exactly the same obstruction. -/
theorem originalObstruction_eq_defect (v : Sections e n o U hU)
    (hv : restriction e n o U hU i v = boundaryCoefficient n o U i E hUE t) :
    originalObstruction e n o U hU i z r s hr hs E hE hUE t ht hUa =
      defect e n o U hU i v :=
  defect_eq_of_restriction_eq e n o U hU i
    ((liftFamily_restriction e n o U hU i z r s hr hs E hE hUE t ht hUa).trans hv.symm)

/-- Vanishing is equivalent to actual compatible invariant lifts of the unchanged open section. -/
theorem originalObstruction_eq_zero_iff :
    originalObstruction e n o U hU i z r s hr hs E hE hUE t ht hUa = 0 ↔
      ∃ v : Sections e n o U hU,
        restriction e n o U hU i v = boundaryCoefficient n o U i E hUE t ∧
          ∀ a b, (mixedChartFirst (o a) (o b) (U a) (U b)).appTop (v a).val =
            (mixedChartSecond (o a) (o b) (U a) (U b)).appTop (v b).val := by
  rw [originalObstruction, defect_eq_zero_iff_compatible, liftFamily_restriction]

variable [Etale p]

include hr hs ht in
omit [IsClosedImmersion i] in
/-- Every actual lift family's discrepancy belongs to the exact original boundary kernel. -/
theorem lift_family_difference_mem_kernel (v : Sections e n o U hU)
    (hv : restriction e n o U hU i v = boundaryCoefficient n o U i E hUE t) (a b : ι) :
    difference e n o U hU v a b ∈
      RingHom.ker (mixedChartBoundaryInclusion (o a) (o b) (U a) (U b) i).appTop.hom :=
  mixedChart_lifts_sub_mem_kernel e (o a) (o b) (U a) (U b) i z r s hr hs
    E hE (hUE a) (hUE b) t ht (v a).val (v b).val (congrFun hv a) (congrFun hv b)

/-- In particular the constructed representative retains all nilpotents of every boundary. -/
theorem liftFamily_difference_mem_kernel (a b : ι) :
    difference e n o U hU (liftFamily e n o U hU i z r s hr hs E hE hUE t ht hUa) a b ∈
      RingHom.ker (mixedChartBoundaryInclusion (o a) (o b) (U a) (U b) i).appTop.hom :=
  lift_family_difference_mem_kernel e n o U hU i z r s hr hs E hE hUE t ht _
    (liftFamily_restriction e n o U hU i z r s hr hs E hE hUE t ht hUa) a b

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
