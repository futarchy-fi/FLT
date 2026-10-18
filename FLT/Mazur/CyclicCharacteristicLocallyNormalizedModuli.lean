/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSheaf
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Original modular objects admitting parameters fppf locally

Take the local closure of the actual unmarked image inside the original
modular-class presheaf. Every original smooth ample cyclic object lies in
this subpresheaf. Descent gives a natural transformation from these original
classes to the constructed unmarked sheaf, retaining all global parameters.
The local closure is not asserted to be a sheaf itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original modular classes which have an actual global parameter. -/
def normalizedModuliImage : Subfunctor (ampleCyclicClassPresheaf n) :=
  Subfunctor.range (unmarkedParameterModuliMap n)

/-- The original modular classes which have actual parameters fppf locally. -/
def locallyNormalizedModuli : Subfunctor (ampleCyclicClassPresheaf n) :=
  (normalizedModuliImage n).sheafify Scheme.fppfTopology

/-- The unmarked quotient embeds into the unchanged original modular-class presheaf. -/
instance unmarkedParameterModuliMap_mono : Mono (unmarkedParameterModuliMap n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  exact (mono_iff_injective _).mpr (unmarkedParameterClassMap_injective n T.unop)

/-- Original smooth ample cyclic objects belong to the local normalized image. -/
theorem smooth_mem_locallyNormalizedModuli {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩ ∈ (locallyNormalizedModuli n).obj (Opposite.op S) := by
  obtain ⟨C, z, hz⟩ := exists_unmarkedParameterClass_fppf_cover n H hc ha
  apply Scheme.fppfTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro T g ⟨i⟩
  exact ⟨z i, hz i⟩

/-- A globally normalized original class has its unique pointwise quotient class. -/
def normalizedModuliImageToSheaf :
    (normalizedModuliImage n).toFunctor ⟶ (unmarkedParameterSheaf n).obj :=
  inv (Subfunctor.toRange (unmarkedParameterModuliMap n)) ≫ unmarkedClassToSheaf n

/-- Global image descent retains every unmarked parameter class. -/
theorem normalizedModuliImageToSheaf_class :
    Subfunctor.toRange (unmarkedParameterModuliMap n) ≫ normalizedModuliImageToSheaf n =
      unmarkedClassToSheaf n := by
  unfold normalizedModuliImageToSheaf
  rw [IsIso.hom_inv_id_assoc]

/-- Original locally normalized classes descend naturally to the actual unmarked fppf sheaf. -/
def locallyNormalizedModuliMap :
    (locallyNormalizedModuli n).toFunctor ⟶ (unmarkedParameterSheaf n).obj :=
  (normalizedModuliImage n).sheafifyLift (normalizedModuliImageToSheaf n)
    ((isSheaf_iff_isSheaf_of_type _ _).mp (unmarkedParameterSheaf n).property)

/-- Descent on the local closure agrees with its originally defined global image map. -/
theorem locallyNormalizedModuliMap_global :
    Subfunctor.homOfLe ((normalizedModuliImage n).le_sheafify Scheme.fppfTopology) ≫
      locallyNormalizedModuliMap n = normalizedModuliImageToSheaf n :=
  Subfunctor.to_sheafifyLift _ _ _

/-- The natural transformation on original local classes retains every actual quotient class. -/
theorem locallyNormalizedModuliMap_class :
    Subfunctor.toRange (unmarkedParameterModuliMap n) ≫
      Subfunctor.homOfLe ((normalizedModuliImage n).le_sheafify Scheme.fppfTopology) ≫
        locallyNormalizedModuliMap n = unmarkedClassToSheaf n := by
  rw [locallyNormalizedModuliMap_global, normalizedModuliImageToSheaf_class]

/-- Values on original globally normalized classes determine natural descent uniquely. -/
theorem locallyNormalizedModuliMap_unique
    (d : (locallyNormalizedModuli n).toFunctor ⟶ (unmarkedParameterSheaf n).obj)
    (hd : Subfunctor.homOfLe ((normalizedModuliImage n).le_sheafify Scheme.fppfTopology) ≫ d =
      normalizedModuliImageToSheaf n) : d = locallyNormalizedModuliMap n :=
  (normalizedModuliImage n).to_sheafify_lift_unique
    ((isSheaf_iff_isSheaf_of_type _ _).mp (unmarkedParameterSheaf n).property) _ _
    (hd.trans (locallyNormalizedModuliMap_global n).symm)

end FLT.Mazur.CyclicCharacteristicAtlas
