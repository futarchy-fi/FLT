/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAdicCoverage
public import FLT.Mazur.CyclicAdicSheafQuotient
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Descent on original modular classes locally represented by the enlarged charts

The local image is a subpresheaf of the unchanged original ample cyclic moduli.
It contains every smooth family, the whole actual integral degeneration, and
all prescribed original field one-gon subgroups. Its natural map to the sheaf
quotient retains those classes. Equality with the full moduli presheaf is open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The exact global image inside the original ample cyclic class presheaf. -/
def moduliImage : Subfunctor (ampleCyclicClassPresheaf n) :=
  Subfunctor.range (classModuliMap n)

/-- Original modular classes admitting actual smooth or adic parameters fppf locally. -/
def localModuli : Subfunctor (ampleCyclicClassPresheaf n) :=
  (moduliImage n).sheafify Scheme.fppfTopology

/-- Full compatible parameter classes embed into original modular objects. -/
instance classModuliMap_mono : Mono (classModuliMap n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  exact (mono_iff_injective _).mpr (classMap_injective n T.unop)

/-- Every actual adic test belongs to the unchanged original local modular image. -/
theorem adic_mem_localModuli {T : Scheme} (q : T ⟶ OneGonAdicModuliChart.base) :
    (OneGonAdicModuliChart.moduliMap n).app (Opposite.op T) (ULift.up q) ∈
      (localModuli n).obj (Opposite.op T) :=
  (moduliImage n).le_sheafify Scheme.fppfTopology _ ⟨adicClass n q, rfl⟩

/-- The actual complete-base class itself belongs to the local image. -/
theorem integral_mem_localModuli :
    OneGonAdicCharacterTower.integralCanonicalLevelClass n ∈
      (localModuli n).obj (Opposite.op OneGonAdicModuliChart.base) := by
  have h := adic_mem_localModuli n (𝟙 OneGonAdicModuliChart.base)
  change ampleCyclicClassesPullback (𝟙 OneGonAdicModuliChart.base) n
    (OneGonAdicCharacterTower.integralCanonicalLevelClass n) ∈
      (localModuli n).obj (Opposite.op OneGonAdicModuliChart.base) at h
  rwa [ampleCyclicClassesPullback_id] at h

/-- Every original smooth ample cyclic family has a local presentation in the enlarged charts. -/
theorem smooth_mem_localModuli {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩ ∈ (localModuli n).obj (Opposite.op S) := by
  obtain ⟨C, z, hz⟩ := smooth_cover n H hc ha
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨z i, hz i⟩

/-- Every prescribed original field one-gon subgroup belongs to the enlarged local image. -/
theorem prescribed_boundary_mem_localModuli (K : Type) [Field K]
    (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
      (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
      (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)
    (hc : H.IsCyclic) (ha : H.IsAmple) :
    Quotient.mk _ (⟨⟨_, H⟩, hc, ha⟩ : ampleCyclicLevels (Spec (.of K)) n) ∈
      (localModuli n).obj (Opposite.op (Spec (.of K))) := by
  have h := adic_mem_localModuli n (IntegralOneGonSpecializations.boundaryMap K)
  rw [← adicClass_moduli, prescribed_boundary_class n K H hc ha] at h
  exact h

/-- Recover the unique global parameter class and pass it to the actual sheaf quotient. -/
def imageToSheaf : (moduliImage n).toFunctor ⟶ (quotientSheaf n).obj :=
  inv (Subfunctor.toRange (classModuliMap n)) ≫ classToSheaf n

/-- Global descent retains each full compatible class. -/
theorem imageToSheaf_class :
    Subfunctor.toRange (classModuliMap n) ≫ imageToSheaf n = classToSheaf n := by
  unfold imageToSheaf
  rw [IsIso.hom_inv_id_assoc]

/-- Descent on original locally represented modular objects. -/
def localModuliMap : (localModuli n).toFunctor ⟶ (quotientSheaf n).obj :=
  (moduliImage n).sheafifyLift (imageToSheaf n)
    ((isSheaf_iff_isSheaf_of_type _ _).mp (quotientSheaf n).property)

/-- Local descent agrees with the specified actual global classes. -/
theorem localModuliMap_global :
    Subfunctor.homOfLe ((moduliImage n).le_sheafify Scheme.fppfTopology) ≫
      localModuliMap n = imageToSheaf n := Subfunctor.to_sheafifyLift _ _ _

/-- The original local-class transformation retains every actual chart quotient class. -/
theorem localModuliMap_class :
    Subfunctor.toRange (classModuliMap n) ≫
      Subfunctor.homOfLe ((moduliImage n).le_sheafify Scheme.fppfTopology) ≫
        localModuliMap n = classToSheaf n := by
  rw [localModuliMap_global, imageToSheaf_class]

end FLT.Mazur.CyclicAdicParameters
