/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicGroupScheme
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Extension and specialization of points of the proper cubic group -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The spectrum of an algebra, viewed over the coefficient base. -/
abbrev pointSource (S : Type u) [CommRing S] [Algebra R S] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The coefficient morphism from an algebra point to the terminal object over the base. -/
def pointSourceToUnit (S : Type u) [CommRing S] [Algebra R S] :
    pointSource (R := R) S ⟶ 𝟙_ (Over (Spec (.of R))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R S))) (by simp)

/-- A section of the cubic restricts to an algebra-valued point by precomposition. -/
def sectionRestriction [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    (S : Type u) [CommRing S] [Algebra R S] :
    (𝟙_ (Over (Spec (.of R))) ⟶ groupModel W) →*
      (pointSource (R := R) S ⟶ groupModel W) :=
  ((yonedaGrpObj (groupModel W)).map (pointSourceToUnit (R := R) S).op).hom

@[simp] theorem sectionRestriction_apply
    [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    (S : Type u) [CommRing S] [Algebra R S]
    (s : 𝟙_ (Over (Spec (.of R))) ⟶ groupModel W) :
    sectionRestriction W S s = pointSourceToUnit (R := R) S ≫ s := rfl

/-- Every generic point over a valuation ring extends to a section of the proper cubic. -/
theorem genericPoint_extends [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (p : pointSource (R := R) K ⟶ groupModel W) :
    ∃ s : 𝟙_ (Over (Spec (.of R))) ⟶ groupModel W,
      pointSourceToUnit (R := R) K ≫ s = p := by
  have hproper : IsProper (toBase W) := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hproper
  have hv : ValuativeCriterion (toBase W) := hproper.1.1.1
  let sq : ValuativeCommSq (toBase W) :=
    { R := R
      K := K
      i₁ := p.left
      i₂ := 𝟙 _
      commSq := ⟨by simpa using p.w⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hv.existence sq).exists_lift
  refine ⟨Over.homMk l hl₂, ?_⟩
  apply Over.OverMorphism.ext
  exact hl₁

/-- Generic restriction is injective by separatedness and the injective map
from the valuation ring to its fraction field. -/
theorem genericRestriction_injective
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective (fun (s : 𝟙_ (Over (Spec (.of R))) ⟶ groupModel W) ↦
      pointSourceToUnit (R := R) K ≫ s) := by
  intro s t h
  apply Over.OverMorphism.ext
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsSchemeTheoreticallyDominant j :=
    specMap_schematic_dominance _ (IsFractionRing.injective R K)
  apply hom_ext_of_schematic_dominance (toBase W) (s.w.trans t.w.symm) j
  exact congrArg Over.Hom.left h

/-- Properness makes generic restriction an isomorphism of groups, not only a pointwise lift. -/
def genericRestrictionEquiv [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    (𝟙_ (Over (Spec (.of R))) ⟶ groupModel W) ≃*
      (pointSource (R := R) K ⟶ groupModel W) :=
  MulEquiv.ofBijective (sectionRestriction W K)
    ⟨genericRestriction_injective W, genericPoint_extends W⟩

/-- Specialization from the fraction field to any field algebra of the valuation ring:
extend by properness and then restrict the resulting section. -/
def specializationHom [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Field k] [Algebra R k] :
    (pointSource (R := R) K ⟶ groupModel W) →*
      (pointSource (R := R) k ⟶ groupModel W) :=
  (sectionRestriction W k).comp (genericRestrictionEquiv W K).symm.toMonoidHom

theorem specializationHom_section [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    [Field k] [Algebra R k]
    (s : 𝟙_ (Over (Spec (.of R))) ⟶ groupModel W) :
    specializationHom W K k (sectionRestriction W K s) = sectionRestriction W k s := by
  change sectionRestriction W k
    ((genericRestrictionEquiv W K).symm ((genericRestrictionEquiv W K) s)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The classical point law maps to the actual group of scheme-valued points. -/
def classicalPointHom [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K] :
    Multiplicative ((W.map (algebraMap R K)).toAffine.Point) →*
      (pointSource (R := R) K ⟶ groupModel W) where
  toFun P := Over.homMk (fieldPointMorphism W P.toAdd) (fieldPointMorphism_toBase W P.toAdd)
  map_one' := by
    apply Over.OverMorphism.ext
    rfl
  map_mul' P Q := by
    apply Over.OverMorphism.ext
    exact (fieldPointPair_add W P.toAdd Q.toAdd).symm

/-- Specialize a classical generic-fiber point through its unique integral section. -/
def classicalSpecializationHom [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    [Field k] [Algebra R k] :
    Multiplicative ((W.map (algebraMap R K)).toAffine.Point) →*
      (pointSource (R := R) k ⟶ groupModel W) :=
  (specializationHom W K k).comp (classicalPointHom W K)

/-- Specialization preserves every torsion relation, without requiring
integral ordinary-affine coordinates. -/
theorem classicalSpecializationHom_torsion [IsDomain R] [ValuationRing R]
    [IsNoetherianRing R] [W.IsElliptic]
    (K k : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    [Field k] [Algebra R k]
    (P : (W.map (algebraMap R K)).toAffine.Point) (n : ℕ) (h : n • P = 0) :
    classicalSpecializationHom W K k (Multiplicative.ofAdd P) ^ n = 1 := by
  rw [← map_pow]
  have hh : Multiplicative.ofAdd P ^ n = 1 := congrArg Multiplicative.ofAdd h
  rw [hh, map_one]

end WeierstrassCurve.CubicCharts
