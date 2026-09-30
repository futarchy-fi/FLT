/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowSimultaneousLineBundle
public import FLT.Mazur.CoherentClosedPushforward
public import FLT.Mazur.CoherentGenericCoordinates

/-!
# Generic restriction of Chow witnesses

Over the actual dense isomorphism open, the direct image of every natural power
is the line bundle transported by the inverse scheme isomorphism. At the generic
point of an integral source, the maximal ideal vanishes and the actual stalk has
dimension one for its canonical residue-field action. No coherence of the full
direct image or cohomology comparison is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericIdealEmbedding
open FLT.Mazur.AnnihilatorSubsheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Open base change followed by transport through the actual Chow isomorphism. -/
def graphPowerCommonIso (n : ℕ) :
    ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).restrict
        (chartData f).common.ι ≅
      ((graphLineBundlePower f n).restrict
        (graphClosureπ f ⁻¹ᵁ (chartData f).common).ι).restrict
          (graphClosureCommonIso f).inv :=
  (closedPushforwardRestriction (graphClosureπ f) (chartData f).common).app _ ≪≫
    (pushforwardIsoRestrictInverse (graphClosureCommonIso f)).app _

/-- Every power of the witness has local rank one on the specified dense open. -/
theorem graphPowerCommon_locallyFreeRankOne (n : ℕ) :
    LocallyFreeRankOne
      (((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).restrict
        (chartData f).common.ι) :=
  (((graphLineBundlePower_locallyFreeRankOne f n).restrict _).restrict _).of_iso
    (graphPowerCommonIso f n).symm

end FLT.Mazur.Chow

namespace FLT.Mazur.FCurve

variable {X Y : Scheme}

/-- A local isomorphism induces a linear equivalence on the original ambient stalks. -/
def openStalkLinearEquiv (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    {M N : X.Modules} (e : M.restrict j ≅ N.restrict j) :
    M.presheaf.stalk (j y) ≃ₗ[X.presheaf.stalk (j y)] N.presheaf.stalk (j y) := by
  let a := comparisonRestrictStalk j y M
  let b := comparisonRestrictStalk j y N
  let c := comparisonStalkEquiv e y
  refine { toAddEquiv := a.symm.trans (c.toAddEquiv.trans b), map_smul' := ?_ }
  intro r m
  obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap y))).surjective r
  obtain ⟨v, rfl⟩ := a.surjective m
  change b (c (a.symm (inv (j.stalkMap y) s • a v))) =
    inv (j.stalkMap y) s • b (c (a.symm (a v)))
  rw [← comparisonRestrictStalk_smul, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply, c.map_smul]
  exact comparisonRestrictStalk_smul j y N s (c v)

/-- A local rank-one trivialization gives coordinates on the actual ambient stalk. -/
def lineStalkCoordinates (M : X.Modules) (hM : LocallyFreeRankOne M) (x : X) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let U := (hM x).choose
  have hx := (hM x).choose_spec.1
  let e := (hM x).choose_spec.2.some
  let t : M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (structureModule X).presheaf.stalk x :=
    openStalkLinearEquiv U.ι ⟨x, hx⟩ (e ≪≫ (restrictUnitIso U.ι).symm)
  exact t.trans (structureStalkLinearEquiv x)

/-- At an integral generic point every module stalk is annihilated by the maximal ideal. -/
theorem genericStalkAnnihilated [IsIntegral X] (M : X.Modules) :
    StalkAnnihilated M (genericPoint X) := by
  intro r hr m
  have hzero : r = 0 := by
    change r ∈ IsLocalRing.maximalIdeal X.functionField at hr
    simpa only [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] using hr
  rw [hzero, zero_smul]

/-- Rank-one coordinates over the generic local ring are linear for the residue action. -/
def genericResidueCoordinates [IsIntegral X] (M : X.Modules)
    (e : M.presheaf.stalk (genericPoint X) ≃ₗ[X.functionField] X.functionField) :
    letI := residueModule M (genericPoint X) (genericStalkAnnihilated M)
    M.presheaf.stalk (genericPoint X) ≃ₗ[X.residueField (genericPoint X)]
      X.residueField (genericPoint X) := by
  letI := residueModule M (genericPoint X) (genericStalkAnnihilated M)
  let q : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      ⟨(X.residue (genericPoint X)).hom.injective, IsLocalRing.residue_surjective⟩
  refine { toAddEquiv := e.toAddEquiv.trans q.toAddEquiv, map_smul' := ?_ }
  intro r m
  obtain ⟨s, rfl⟩ := q.surjective r
  change q (e ((X.residue (genericPoint X)) s • m)) = q s * q (e m)
  rw [residue_smul, e.map_smul]
  exact q.map_mul s (e m)

end FLT.Mazur.FCurve

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The canonical residue action on the actual direct-image generic stalk is defined. -/
theorem graphPower_genericStalkAnnihilated [IsIntegral X] (n : ℕ) :
    StalkAnnihilated ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n))
      (genericPoint X) := genericStalkAnnihilated _

/-- The original direct-image stalk has rank one over the generic local ring. -/
def graphPowerGenericCoordinates [IsIntegral X] (n : ℕ) :
    ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).presheaf.stalk
        (genericPoint X) ≃ₗ[X.functionField] X.functionField := by
  let M := (pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)
  let U := (chartData f).common
  let x : U.toScheme := ⟨genericPoint X, graphCommon_genericPoint f⟩
  let h := graphPowerCommon_locallyFreeRankOne f n x
  let V := h.choose
  have hx := h.choose_spec.1
  let e := h.choose_spec.2.some
  let j := V.ι ≫ U.ι
  let y : V.toScheme := ⟨x, hx⟩
  let t : M.restrict j ≅ (structureModule X).restrict j :=
    (restrictFunctorComp V.ι U.ι).app M ≪≫ e ≪≫ (restrictUnitIso j).symm
  let c : M.presheaf.stalk (genericPoint X) ≃ₗ[X.functionField]
      (structureModule X).presheaf.stalk (genericPoint X) := openStalkLinearEquiv j y t
  exact c.trans (structureStalkLinearEquiv (genericPoint X))

/-- The generic residue dimension is one for the action supplied by the annihilation proof. -/
theorem graphPower_generic_finrank [IsIntegral X] (n : ℕ) :
    let := residueModule ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n))
      (genericPoint X) (graphPower_genericStalkAnnihilated f n)
    Module.finrank (X.residueField (genericPoint X))
      (((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).presheaf.stalk
        (genericPoint X)) = 1 := by
  let := residueModule ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n))
    (genericPoint X) (graphPower_genericStalkAnnihilated f n)
  exact (genericResidueCoordinates _ (graphPowerGenericCoordinates f n)).finrank_eq.trans
    (Module.finrank_self _)

end FLT.Mazur.Chow
