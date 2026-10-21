/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleModuli
public import FLT.Mazur.CyclicBoundaryOriginalTestCoverage
public import FLT.Mazur.CompatibleSubgroupAmple
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# Original ample cyclic tests lift to the unrestricted ample chart

An actual compatible subgroup comparison transports ampleness to the
universal pullback. Its unique lift to the constructed ample open retains
the entire original curve and subgroup, with no faithful-marking hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
  {F : GeneralizedEllipticCurve T} (H : F.FiniteSubgroup n)
  (k : T ⟶ unrestrictedMultiplicationLocus E n)
  (d : CompatibleIso H ((unrestrictedLocusSubgroup E n).baseChange k)) (ha : H.IsAmple)

/-- An original ample test factors through the actual unrestricted ample open. -/
def unrestrictedAmpleLift : T ⟶ (unrestrictedAmpleOpen E n).toScheme :=
  (unrestrictedLocusSubgroup E n).ampleOpenLift (unrestrictedLocusGenerator_cartier E n).2.1.1
    k (d.isAmple ha)

/-- The ample lift keeps the original closed-locus parameter unchanged. -/
@[reassoc] theorem unrestrictedAmpleLift_inclusion :
    unrestrictedAmpleLift E n H k d ha ≫ (unrestrictedAmpleOpen E n).ι = k :=
  (unrestrictedLocusSubgroup E n).ampleOpenLift_inclusion _ _ _

/-- Its full subgroup comparison uses the original factorization of base maps. -/
def unrestrictedAmpleLiftSubgroupIso :
    CompatibleIso H ((unrestrictedAmpleLevel E n).val.2.baseChange
      (unrestrictedAmpleLift E n H k d ha)) :=
  d.trans ((unrestrictedLocusSubgroup E n).compatibleBaseChangeCompEq
    (unrestrictedAmpleOpen E n).ι (unrestrictedAmpleLift E n H k d ha) k
    (unrestrictedAmpleLift_inclusion E n H k d ha).symm)

/-- The full curve comparison is the original comparison followed by actual base change. -/
theorem unrestrictedAmpleLiftSubgroupIso_curve :
    (unrestrictedAmpleLiftSubgroupIso E n H k d ha).curve =
      d.curve ≪≫ (unrestrictedLocusCurve E n).baseChangeCompEqIso
        (unrestrictedAmpleOpen E n).ι (unrestrictedAmpleLift E n H k d ha) k
        (unrestrictedAmpleLift_inclusion E n H k d ha).symm := by
  change d.curve ≪≫ _ = _
  rw [compatibleBaseChangeCompEq_curve]

/-- Uniqueness is on actual scheme morphisms, including nonreduced test schemes. -/
theorem unrestrictedAmpleLift_unique (v : T ⟶ (unrestrictedAmpleOpen E n).toScheme)
    (hv : v ≫ (unrestrictedAmpleOpen E n).ι = k) :
    v = unrestrictedAmpleLift E n H k d ha := by
  apply (cancel_mono (unrestrictedAmpleOpen E n).ι).mp
  rw [hv, unrestrictedAmpleLift_inclusion]

/-- Ample cyclic subgroups on original tests are covered by the unrestricted ample chart. -/
theorem exists_original_unrestricted_ample_test (g : T ⟶ S)
    (H : (E.baseChange g).FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ v : U ⟶ (unrestrictedAmpleOpen E n).toScheme,
        Nonempty (CompatibleIso (H.baseChange q)
          ((unrestrictedAmpleLevel E n).val.2.baseChange v)) := by
  obtain ⟨U, q, hf, hs, hl, P, hP, k, d, _⟩ :=
    exists_original_unrestricted_test E n g H hc 1 1
  exact ⟨U, q, hf, hs, hl, unrestrictedAmpleLift E n (H.baseChange q) k d (ha.baseChange q),
    ⟨unrestrictedAmpleLiftSubgroupIso E n (H.baseChange q) k d (ha.baseChange q)⟩⟩

end FLT.Mazur.CyclicBoundaryParameter
