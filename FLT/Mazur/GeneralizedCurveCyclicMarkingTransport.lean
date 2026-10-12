/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCyclicSubgroupComparison

/-!
# Faithful cyclic markings through full generalized curve isomorphisms

Transport uses the original group map and reconstructs a compatibly isomorphic
subgroup. Every cyclic section and the original subgroup comparison are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  (e : E ≅ F) (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- Transport the entire cyclic homomorphism through the original group comparison. -/
def transportCyclicMarking : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group) where
  toFun i := φ i ≫ e.hom.group
  map_one' := by rw [map_one, one_comp]
  map_mul' i j := by rw [map_mul, mul_comp]

/-- Each label is carried by the specified original group morphism. -/
theorem transportCyclicMarking_apply (i : Multiplicative (ZMod n)) :
    transportCyclicMarking e φ i = φ i ≫ e.hom.group := rfl

/-- A full curve isomorphism preserves and reflects universal distinctness. -/
theorem transportCyclicMarking_distinct_iff :
    UniversallyDistinct (fun i : ZMod n ↦ transportCyclicMarking e φ (.ofAdd i)) ↔
      UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)) := by
  constructor
  · intro h V g hV i j hij
    apply h V g hV
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ e.hom.group) hij).trans (Category.assoc _ _ _))
  · intro h V g hV i j hij
    apply h V g hV
    have hi : e.hom.group ≫ e.inv.group = 𝟙 _ :=
      congrArg (fun f ↦ f.group) e.hom_inv_id
    have hh := congrArg (fun f ↦ f ≫ e.inv.group) hij
    simpa only [transportCyclicMarking_apply, Category.assoc, hi, Category.comp_id] using hh

variable [NeZero n] (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))

/-- Reconstruction after transport retains the full original curve and subgroup. -/
def transportCyclicMarkingCompatibleIso :
    FiniteSubgroup.CompatibleIso (E.relativeCyclicSubgroup φ hφ)
      (F.relativeCyclicSubgroup (transportCyclicMarking e φ)
        ((transportCyclicMarking_distinct_iff e φ).mpr hφ)) :=
  relativeCyclicSubgroupCompatibleIso φ (transportCyclicMarking e φ) hφ
    ((transportCyclicMarking_distinct_iff e φ).mpr hφ) e (fun _ ↦ rfl)

/-- An existing comparison to an original subgroup survives transport of the full marking. -/
def transportCyclicMarkingOriginalIso (H : E.FiniteSubgroup n)
    (a : FiniteSubgroup.CompatibleIso (E.relativeCyclicSubgroup φ hφ) H) :
    FiniteSubgroup.CompatibleIso
      (F.relativeCyclicSubgroup (transportCyclicMarking e φ)
        ((transportCyclicMarking_distinct_iff e φ).mpr hφ)) H :=
  (transportCyclicMarkingCompatibleIso e φ hφ).symm.trans a

end FLT.Mazur.GeneralizedEllipticCurve
