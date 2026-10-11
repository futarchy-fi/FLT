/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAcyclicUniversalRecovery
public import FLT.Mazur.AcyclicDivisorDegreePresheaf

/-!
# The acyclic degree-d divisor functor has an actual representing scheme

For a proper smooth geometrically integral curve with an ample line, the
constructed open in the Hilbert scheme represents all full acyclic divisors
of degree d. The universal family is the original full Hilbert ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.FCurve FLT.Mazur.ClosedIdealCover
open FLT.Mazur.SchemePicard FLT.Mazur.CartierAbel
namespace FLT.Mazur.HilbertChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z] [Flat z]
  [GeometricallyIntegral z] [SmoothOfRelativeDimension 1 z] (d : ℕ)

/-- The actual Hilbert family on the parameter open has the specified degree on every test. -/
def acyclicHilbertDegreeMap (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest z d) :
    (acyclicDivisorDegreeSubfunctor z d).toFunctor.obj (op T) :=
  ⟨acyclicHilbertParameterDivisor z d T k, hilbertPicardIdeal_degree z d T _⟩

variable {L : Z.Modules} (hL : AmpleLineBundle L)

include hL in
/-- Full divisor ideals distinguish all actual maps to the acyclic parameter scheme. -/
theorem acyclicHilbertDegreeMap_injective (T : Over (Spec (.of R))) :
    Function.Injective (acyclicHilbertDegreeMap z d T) := by
  intro k l h
  have hi := congrArg (fun D ↦ D.val.val.val) h
  have hf : (ampleHilbertFamilyEquiv z hL d T) (k ≫ acyclicHilbertArrow z d) =
      (ampleHilbertFamilyEquiv z hL d T) (l ≫ acyclicHilbertArrow z d) := by
    apply Subtype.ext
    change ((allAffineAmbientCharts z).parameterFamily d T.hom
      (ampleHilbertParameterEquiv z d T (k ≫ acyclicHilbertArrow z d))).val =
      ((allAffineAmbientCharts z).parameterFamily d T.hom
        (ampleHilbertParameterEquiv z d T (l ≫ acyclicHilbertArrow z d))).val
    have hh := congrArg (fun I ↦ I.comap (pullbackSymmetry z T.hom).inv) hi
    simpa only [acyclicHilbertDegreeMap, acyclicHilbertParameterDivisor,
      relativeDivisorOfLocalAcyclic, AmbientQuotientCharts.parameterPicardDivisor,
      AmbientQuotientCharts.parameterPicardIdeal, ← Scheme.IdealSheafData.comap_comp,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id] using hh
  have hk := (ampleHilbertFamilyEquiv z hL d T).injective hf
  apply Over.OverMorphism.ext
  exact (cancel_mono (acyclicHilbertArrow z d).left).mp (congrArg Over.Hom.left hk)

include hL in
/-- Every full acyclic degree-d divisor has an actual parameter in the constructed open. -/
theorem acyclicHilbertDegreeMap_surjective (T : Over (Spec (.of R))) :
    Function.Surjective (acyclicHilbertDegreeMap z d T) := by
  intro D
  let J := acyclicDegreeHilbertFamily z d T D
  let k := (ampleHilbertFamilyEquiv z hL d T).symm J
  have hk : (allAffineAmbientCharts z).parameterFamily d T.hom
      (ampleHilbertParameterEquiv z d T k) = J :=
    (ampleHilbertFamilyEquiv z hL d T).apply_symm_apply J
  have hi : (allAffineAmbientCharts z).parameterPicardIdeal d T
      (ampleHilbertParameterEquiv z d T k) = D.val.val.val := by
    unfold AmbientQuotientCharts.parameterPicardIdeal
    rw [hk]
    exact acyclicDegreeHilbertFamily_recover z d T D
  have hd : (allAffineAmbientCharts z).parameterPicardDivisor d T
      (ampleHilbertParameterEquiv z d T k) = D.val.val := Subtype.ext hi
  have hm : (allAffineAmbientCharts z).parameterAbelClass d T
      (ampleHilbertParameterEquiv z d T k) ∈
      (localGeometricAcyclicFppfSubfunctor z).obj (op T) := by
    unfold AmbientQuotientCharts.parameterAbelClass
    rw [hd]
    exact (relativeDivisor_localAcyclic_iff z T D.val.val D.val.property.1).mpr D.val.property.2
  obtain ⟨l, hl, _⟩ := (acyclicHilbert_represents z d T k).mp hm
  refine ⟨l, Subtype.ext (acyclicRankOneRelativeDivisor_ext ?_)⟩
  change (allAffineAmbientCharts z).parameterPicardIdeal d T
    (ampleHilbertParameterEquiv z d T (l ≫ acyclicHilbertArrow z d)) = D.val.val.val
  rw [hl]
  exact hi

/-- All maps to the actual open classify the full acyclic degree-d divisors. -/
def acyclicHilbertDegreeEquiv (T : Over (Spec (.of R))) :
    (T ⟶ acyclicHilbertTest z d) ≃ (acyclicDivisorDegreeSubfunctor z d).toFunctor.obj (op T) :=
  Equiv.ofBijective (acyclicHilbertDegreeMap z d T)
    ⟨acyclicHilbertDegreeMap_injective z d hL T, acyclicHilbertDegreeMap_surjective z d hL T⟩

/-- The actual open parameter scheme represents the full acyclic degree-d divisor presheaf. -/
def acyclicHilbertDivisorIso :
    yoneda.obj (acyclicHilbertTest z d) ≅ (acyclicDivisorDegreeSubfunctor z d).toFunctor :=
  NatIso.ofComponents (fun T ↦ (acyclicHilbertDegreeEquiv z d hL T.unop).toIso)
    (fun {T U} g ↦ by
      apply ConcreteCategory.hom_ext
      intro k
      apply Subtype.ext
      change acyclicHilbertParameterDivisor z d U.unop (g.unop ≫ k) =
        finiteTypeAcyclicDivisorMap z g.unop (acyclicHilbertParameterDivisor z d T.unop k)
      rw [acyclicHilbertParameterDivisor_eq, acyclicHilbertParameterDivisor_eq,
        finiteTypeAcyclicDivisorMap_comp])

/-- The representation is pullback of the original full universal acyclic ideal. -/
lemma acyclicHilbertDivisorIso_ideal (T : Over (Spec (.of R)))
    (k : T ⟶ acyclicHilbertTest z d) :
    ((acyclicHilbertDivisorIso z d hL).hom.app (op T) k).val.val.val =
      (acyclicHilbertDivisor z d).val.val.comap (relativeTotalMap z k) :=
  acyclicHilbertParameterDivisor_ideal z d T k

end FLT.Mazur.HilbertChart
