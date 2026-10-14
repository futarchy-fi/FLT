/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionSmoothLift
public import FLT.Mazur.PolygonCompleteGenericSmooth

/-!
# A finite original-node cover for extending the identity action

Every input not covered by the constructed smooth lift has one of the actual
original nodes as its second coordinate. Choose actual affine neighborhoods
of those nodes and pull them back to cover the remaining action inputs.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "X" => exactVeroneseProj K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "j" => completeClosedFiberInclusion K n h

/-- Every nonsmooth point of the entire original family is one of its original nodes. -/
theorem complete_nonsmooth_eq_node (x : X) (hx : x ∉ (π).smoothLocus) :
    ∃ i, x = completeNode K n h i := by
  have ht : PowerSeries.X ∈ ((π) x).asIdeal := by
    by_contra ht
    exact hx (complete_mem_smoothLocus_of_parameter_notMem K n h x ht)
  have hb : (π) x = IsLocalRing.closedPoint (PowerSeries K) := by
    apply PrimeSpectrum.ext
    symm
    change IsLocalRing.maximalIdeal (PowerSeries K) = ((π) x).asIdeal
    apply Ideal.IsMaximal.eq_of_le inferInstance ((π) x).isPrime.ne_top
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_le_iff_mem]
    exact ht
  have hr : x ∈ Set.range (j) := by
    rw [completeClosedFiber_range]
    exact hb
  obtain ⟨z, rfl⟩ := hr
  exact completeClosedFiber_nonsmooth_eq_node K n h z hx

/-- An actual affine neighborhood of each specified original node. -/
def completeActionNodeAffine (i : Fin n) : (X).affineOpens :=
  ⟨((X).affineCover.f ((X).affineCover.idx (completeNode K n h i))).opensRange,
    isAffineOpen_opensRange _⟩

/-- The chosen neighborhood contains the unchanged original node. -/
theorem completeActionNodeAffine_mem (i : Fin n) :
    completeNode K n h i ∈ (completeActionNodeAffine K n h i).1 :=
  (X).affineCover.covers (completeNode K n h i)

/-- The original smooth open together with one actual affine neighborhood per original node. -/
def completeActionExtensionOpen : Option (Fin n) → (X).Opens
  | none => (π).smoothLocus
  | some i => (completeActionNodeAffine K n h i).1

/-- These are an actual finite cover of the entire original family. -/
theorem completeActionExtensionOpen_cover (x : X) :
    ∃ i, x ∈ completeActionExtensionOpen K n h i := by
  by_cases hx : x ∈ (π).smoothLocus
  · exact ⟨none, hx⟩
  · obtain ⟨i, rfl⟩ := complete_nonsmooth_eq_node K n h x hx
    exact ⟨some i, completeActionNodeAffine_mem K n h i⟩

/-- The finite extension atlas retains each original open as an actual scheme. -/
def completeActionExtensionCover : (X).OpenCover where
  I₀ := Option (Fin n)
  «X» i := (completeActionExtensionOpen K n h i).toScheme
  f i := (completeActionExtensionOpen K n h i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨i, hi⟩ := completeActionExtensionOpen_cover K n h x
    exact ⟨i, ⟨x, hi⟩, rfl⟩

local notation "s" => completeIdentityActionSecond K n h

/-- The unchanged whole input product's extension domains, with the full identity parameter. -/
def completeIdentityActionExtensionOpen (i : Option (Fin n)) :
    (completeIdentityActionProduct K n h 0).Opens :=
  (s) ⁻¹ᵁ completeActionExtensionOpen K n h i

/-- The first extension chart is exactly the entire domain of the constructed smooth lift. -/
theorem completeIdentityActionExtensionOpen_none :
    completeIdentityActionExtensionOpen K n h none = completeIdentityActionSmoothOpen K n h :=
  rfl

/-- The extension domains cover every original action input, including all singular inputs. -/
def completeIdentityActionExtensionCover : (completeIdentityActionProduct K n h 0).OpenCover where
  I₀ := Option (Fin n)
  «X» i := (completeIdentityActionExtensionOpen K n h i).toScheme
  f i := (completeIdentityActionExtensionOpen K n h i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨i, hi⟩ := completeActionExtensionOpen_cover K n h ((s) x)
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- Every still-uncovered input has an actual original node as its second coordinate. -/
theorem completeIdentityAction_not_smooth_eq_node
    (x : completeIdentityActionProduct K n h 0)
    (hx : x ∉ completeIdentityActionSmoothOpen K n h) :
    ∃ i, (s) x = completeNode K n h i :=
  complete_nonsmooth_eq_node K n h ((s) x) hx

end FLT.Mazur.PolygonInfinitesimalStages
