/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryLocusGenerator
public import FLT.Mazur.FiniteSubgroupAmpleComponents
public import FLT.Mazur.AmpleCyclicClassPresheaf

/-!
# The ample open of the unrestricted closed boundary locus

Ampleness cuts out an actual open in the closed multiplication locus. The
original full curve and subgroup define its modular transformation, including
non-etale cyclic subgroups and repeated labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "H" => unrestrictedLocusSubgroup E n
local notation "hI" => And.left (And.left (And.right (unrestrictedLocusGenerator_cartier E n)))

/-- The actual ample open in the unrestricted closed multiplication locus. -/
def unrestrictedAmpleOpen : (unrestrictedMultiplicationLocus E n).Opens := (H).ampleOpen (hI)

/-- The original cyclic subgroup restricted to this open gives an actual ample cyclic level. -/
def unrestrictedAmpleLevel : ampleCyclicLevels (unrestrictedAmpleOpen E n).toScheme n :=
  ⟨⟨(unrestrictedLocusCurve E n).baseChange (unrestrictedAmpleOpen E n).ι,
      (H).baseChange (unrestrictedAmpleOpen E n).ι⟩,
    ((unrestrictedLocusGenerator_cartier E n).isCyclic (H)).baseChange (H) _,
    (H).ampleOpen_isAmple (hI)⟩

/-- The full original ample cyclic class on the constructed unrestricted parameter. -/
def unrestrictedAmpleClass : ampleCyclicClasses (unrestrictedAmpleOpen E n).toScheme n :=
  Quotient.mk _ (unrestrictedAmpleLevel E n)

/-- Arbitrary pullback of the original level gives the actual modular transformation. -/
def unrestrictedAmpleModuliMap : uliftYoneda.{1}.obj (unrestrictedAmpleOpen E n).toScheme ⟶
    ampleCyclicClassPresheaf n where
  app _ := ↾(fun g ↦ ampleCyclicClassesPullback g.down n (unrestrictedAmpleClass E n))
  naturality _ _ f := by
    ext g
    exact congrFun (ampleCyclicClassesPullback_comp g.down f.unop n)
      (unrestrictedAmpleClass E n)

/-- Ampleness is represented exactly by the constructed open on all scheme tests. -/
theorem unrestrictedAmpleOpen_criterion {T : Scheme}
    (g : T ⟶ unrestrictedMultiplicationLocus E n) :
    ((H).baseChange g).IsAmple ↔
      ∃! v : T ⟶ (unrestrictedAmpleOpen E n).toScheme,
        v ≫ (unrestrictedAmpleOpen E n).ι = g :=
  (H).isAmple_iff_existsUnique_ampleOpenLift (hI) g

/-- The actual full divisor meets every component precisely on the ample open. -/
theorem unrestrictedAmpleOpen_components (K : Type) [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ unrestrictedMultiplicationLocus E n) :
    Set.range g ⊆ unrestrictedAmpleOpen E n ↔
      ∀ Z ∈ irreducibleComponents ((unrestrictedLocusCurve E n).baseChange g).curve.left,
        ((((H).baseChange g).ideal.support :
          Set ((unrestrictedLocusCurve E n).baseChange g).curve.left) ∩ Z).Nonempty :=
  (H).range_ampleOpen_iff_meets_components (hI) g

end FLT.Mazur.CyclicBoundaryParameter
