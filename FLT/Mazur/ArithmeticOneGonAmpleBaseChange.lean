/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAmpleParameter
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeModuli

/-!
# Arithmetic one-gon ample charts over arbitrary scheme bases

The full faithful cyclic chart remains ample after arbitrary base change.
Its original modular transformation and actual universal subgroup are retained,
including over mixed-characteristic and nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))
  (n : ℕ) [NeZero n] {T : Scheme} (g : T ⟶ Spec (.of R))
local notation "E" => curve t ht

local instance arithmeticAmplePullbackGroup_separated :
    IsSeparated ((E).baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (E).group.hom g))

local instance arithmeticAmplePullbackGroup_smooth :
    SmoothOfRelativeDimension 1 ((E).baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (E).group.hom g
    inferInstance

local notation "Q" => cyclicFaithfulParameter
  (GeneralizedEllipticCurve.group (GeneralizedEllipticCurve.baseChange (E) g)) n
local notation "q" => faithfulBaseChangeToOriginal g (GeneralizedEllipticCurve.group (E)) n
local notation "I" => ampleParameterOpen (E) n
local notation "J" => ampleParameterOpen (GeneralizedEllipticCurve.baseChange (E) g) n

/-- The actual new-base universal faithful subgroup is ample on its whole parameter scheme. -/
theorem baseChangeFaithfulUniversalSubgroup_isAmple :
    (faithfulUniversalSubgroup ((E).baseChange g) n).IsAmple :=
  (faithfulBaseChangeSubgroupIso g (E) n).isAmple_iff.mpr
    ((faithfulUniversalSubgroup_isAmple t ht n).baseChange (q))

/-- No ample parameters are lost under arbitrary base change of the arithmetic cubic. -/
theorem baseChangeAmpleParameterOpen_eq_top : (J) = ⊤ := by
  rw [ampleParameterOpen_baseChange, ampleParameterOpen_eq_top]
  rfl

/-- The new-base full faithful chart factors canonically through the actual ample chart. -/
def baseChangeFaithfulToAmple : (Q).left ⟶ ampleParameter ((E).baseChange g) n :=
  (faithfulUniversalSubgroup ((E).baseChange g) n).ampleOpenLift
    (faithfulUniversalSubgroup_cartier ((E).baseChange g) n).1 (𝟙 _)
    ((baseChangeFaithfulUniversalSubgroup_isAmple t ht n g).baseChange (𝟙 _))

/-- The factorization retains every actual faithful parameter. -/
@[reassoc] theorem baseChangeFaithfulToAmple_inclusion :
    baseChangeFaithfulToAmple t ht n g ≫ (J).ι = 𝟙 _ :=
  (faithfulUniversalSubgroup ((E).baseChange g) n).ampleOpenLift_inclusion _ _ _

/-- Passing to ample charts commutes with the original faithful base-change projection. -/
@[reassoc] theorem baseChangeFaithfulToAmple_original :
    baseChangeFaithfulToAmple t ht n g ≫ ampleBaseChangeToOriginal g (E) n =
      (q) ≫ faithfulToAmple t ht n := by
  apply (cancel_mono (I).ι).mp
  rw [Category.assoc, ampleBaseChangeToOriginal_inclusion,
    baseChangeFaithfulToAmple_inclusion_assoc,
    Category.assoc, faithfulToAmple_inclusion, Category.comp_id]

/-- The whole faithful arithmetic chart has the original full ample modular transformation. -/
def faithfulBoundaryModuliMap :
    uliftYoneda.{1}.obj (cyclicFaithfulParameter (E).group n).left ⟶
      ampleCyclicClassPresheaf n :=
  uliftYoneda.map (faithfulToAmple t ht n) ≫ ampleModuliMap (E) n

/-- The modular square commutes on every scheme-valued test of the full arithmetic chart. -/
theorem faithfulBoundaryModuliMap_baseChange :
    uliftYoneda.map (baseChangeFaithfulToAmple t ht n g) ≫
      ampleModuliMap ((E).baseChange g) n =
    uliftYoneda.map (q) ≫ faithfulBoundaryModuliMap t ht n := by
  rw [ampleModuliMap_baseChange, ← Category.assoc, ← Functor.map_comp,
    baseChangeFaithfulToAmple_original, Functor.map_comp, Category.assoc]
  rfl

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
