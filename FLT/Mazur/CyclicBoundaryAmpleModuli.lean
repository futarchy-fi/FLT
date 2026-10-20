/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUniversalSubgroup
public import FLT.Mazur.FiniteSubgroupAmpleComponents
public import FLT.Mazur.AmpleCyclicClassPresheaf

/-!
# The boundary parameter's ample open and actual modular transformation

The full original curve and its finite subgroup are retained. Ampleness is
proved on a constructed open and is detected there by geometric component support.
No coverage of arbitrary degenerations is asserted by this boundary chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
local notation "H" => faithfulUniversalSubgroup E n
local notation "hI" => And.left (faithfulUniversalSubgroup_cartier E n)

/-- The actual ample open in the cyclically faithful boundary parameter. -/
def ampleParameterOpen : (cyclicFaithfulParameter E.group n).left.Opens := (H).ampleOpen (hI)

/-- The constructed ample boundary parameter scheme. -/
def ampleParameter : Scheme := (ampleParameterOpen E n).toScheme

/-- The inclusion retains the original ambient boundary parameter. -/
def ampleParameterInclusion : ampleParameter E n ⟶ (parameter E.group n).left :=
  (ampleParameterOpen E n).ι ≫ (cyclicFaithfulInclusion E.group n).left

instance ampleParameterInclusion_isOpenImmersion : IsOpenImmersion (ampleParameterInclusion E n) :=
  inferInstanceAs (IsOpenImmersion
    ((ampleParameterOpen E n).ι ≫ (cyclicFaithfulOpen E.group n).ι))

/-- The original curve and subgroup define an actual ample cyclic level on this open. -/
def ampleUniversalLevel : ampleCyclicLevels (ampleParameter E n) n :=
  ⟨⟨(faithfulUniversalCurve E n).baseChange (ampleParameterOpen E n).ι,
      (H).baseChange (ampleParameterOpen E n).ι⟩,
    (faithfulUniversalSubgroup_isCyclic E n).baseChange (H) _, (H).ampleOpen_isAmple (hI)⟩

/-- The full original boundary family's isomorphism class. -/
def ampleUniversalClass : ampleCyclicClasses (ampleParameter E n) n :=
  Quotient.mk _ (ampleUniversalLevel E n)

/-- The constructed open maps naturally to the original ample cyclic moduli presheaf. -/
def ampleModuliMap : uliftYoneda.{1}.obj (ampleParameter E n) ⟶ ampleCyclicClassPresheaf n where
  app _ := ↾(fun g ↦ ampleCyclicClassesPullback g.down n (ampleUniversalClass E n))
  naturality _ _ f := by
    ext g
    exact congrFun (ampleCyclicClassesPullback_comp g.down f.unop n) (ampleUniversalClass E n)

/-- At its identity test, the modular map is exactly the original constructed level. -/
theorem ampleModuliMap_identity :
    (ampleModuliMap E n).app (Opposite.op (ampleParameter E n)) (ULift.up (𝟙 _)) =
      ampleUniversalClass E n :=
  congrFun (ampleCyclicClassesPullback_id _ n) (ampleUniversalClass E n)

/-- Every ample test of the universal subgroup factors uniquely through the actual open. -/
theorem ampleParameter_criterion {T : Scheme}
    (g : T ⟶ (cyclicFaithfulParameter E.group n).left) :
    ((H).baseChange g).IsAmple ↔
      ∃! v : T ⟶ ampleParameter E n, v ≫ (ampleParameterOpen E n).ι = g :=
  (H).isAmple_iff_existsUnique_ampleOpenLift (hI) g

/-- Geometric membership retains the actual divisor's intersection with every component. -/
theorem ampleParameter_component_criterion (K : Type) [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ (cyclicFaithfulParameter E.group n).left) :
    Set.range g ⊆ ampleParameterOpen E n ↔
      ∀ Z ∈ irreducibleComponents ((faithfulUniversalCurve E n).baseChange g).curve.left,
        ((((H).baseChange g).ideal.support :
          Set ((faithfulUniversalCurve E n).baseChange g).curve.left) ∩ Z).Nonempty :=
  (H).range_ampleOpen_iff_meets_components (hI) g

end FLT.Mazur.CyclicBoundaryParameter
