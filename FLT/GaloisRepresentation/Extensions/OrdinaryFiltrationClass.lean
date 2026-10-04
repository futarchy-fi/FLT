/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltration
public import FLT.GaloisRepresentation.Extensions.ContinuousClass

/-!
# The continuous extension class of an ordinary filtration

Continuity is derived from the middle representation's orbit maps. Exactness
constructs the coefficient cocycle, and changing the section changes it by a
coboundary. The resulting class requires no choice of quotient lift.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions.OrdinaryFiltration

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
    [TopologicalSpace V] [DiscreteTopology V]
    {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)
    (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))

omit [DiscreteTopology k] in
include E hρ in
/-- Quotient equivariance gives continuity of the quotient character. -/
theorem continuous_quotientCharacter : Continuous (fun g : G ↦ (β g : k)) := by
  obtain ⟨w, hw⟩ := E.surjective 1
  have h := (continuous_of_discreteTopology : Continuous E.projection).comp (hρ w)
  simpa only [Function.comp_def, E.projection_equivariant, hw, mul_one] using h

include hρ in
/-- The normalized Hom orbit of every section is continuous. -/
theorem continuous_sectionOrbit (w : V) : Continuous (fun g : G ↦ g • E.sectionOf w) := by
  have hb : Continuous (fun g : G ↦ (β g : k)⁻¹) :=
    (continuous_of_discreteTopology : Continuous (fun a : k ↦ a⁻¹)).comp
      (E.continuous_quotientCharacter hρ)
  have hv : Continuous (fun g : G ↦ (β g : k)⁻¹ • ρ g w) :=
    (continuous_of_discreteTopology : Continuous (fun t : k × V ↦ t.1 • t.2)).comp
      (hb.prodMk (hρ w))
  have hs : Continuous (fun x : V ↦ E.sectionOf x) := continuous_of_discreteTopology
  convert hs.comp hv using 1
  funext g
  apply LinearMap.ext_ring
  change ρ g ((((β g⁻¹ : kˣ) : k) * 1) • w) = (1 : k) • ((β g : k)⁻¹ • ρ g w)
  simp [map_smul]

/-- The actual coefficient cocycle obtained from a vector above one. -/
def cocycleOf (w : V) (hw : E.projection w = 1) :
    ContinuousCocycle G (OrdinaryHomModule α β) :=
  ⟨⟨liftCocycle E.homInjection (E.sectionOf w) (E.section_difference_range w hw),
    continuous_liftCocycle E.homInjection (E.sectionOf w) (E.section_difference_range w hw)
      (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
        continuous_of_discreteTopology E.homInjection_injective
        (fun _ _ ↦ isOpen_discrete _)).isInducing (E.continuous_sectionOrbit hρ w)⟩,
    liftCocycle_isCocycle E.homInjection E.homInjection_injective
      E.homInjection_equivariant (E.sectionOf w) (E.section_difference_range w hw)⟩

/-- The continuous class does not depend on the chosen linear section. -/
theorem classOf_eq (w z : V) (hw : E.projection w = 1) (hz : E.projection z = 1) :
    continuousClassMk (E.cocycleOf hρ w hw) = continuousClassMk (E.cocycleOf hρ z hz) := by
  obtain ⟨a, ha⟩ := E.section_difference w z hw hz
  apply (continuousClassMk_eq_iff _ _).mpr
  refine ⟨a, ?_⟩
  change liftCocycle E.homInjection (E.sectionOf z) _ =
    changeSplitting (liftCocycle E.homInjection (E.sectionOf w) _) a
  symm
  apply liftCocycle_unique E.homInjection E.homInjection_injective
  intro g
  simp only [changeSplitting, map_add, map_sub, E.homInjection_equivariant,
    liftCocycle_spec, ha, smul_add]
  abel

/-- The class extracted from the actual continuous middle representation. -/
def extensionClass : ContinuousClass G (OrdinaryHomModule α β) :=
  continuousClassMk (E.cocycleOf hρ (Classical.choose (E.surjective 1))
    (Classical.choose_spec (E.surjective 1)))

/-- Every section computes the same extracted class. -/
theorem extensionClass_eq (w : V) (hw : E.projection w = 1) :
    E.extensionClass hρ = continuousClassMk (E.cocycleOf hρ w hw) :=
  E.classOf_eq hρ _ w _ hw

end GaloisRepresentation.Extensions.OrdinaryFiltration
