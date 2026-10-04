/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyVanishing
public import FLT.Mazur.ModuleLineTensorExact
public import FLT.Mazur.AmpleAffinePullback

/-!
# Closure properties of eventual positive twist vanishing

Extensions, quotients in short exact sequences, and retracts preserve the
vanishing property used in ampleness descent. No kernel-closure assertion is
made: degree-one kernel cohomology also requires surjectivity in degree zero.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorCurrying ModuleLineBundleTensorPullback

local instance eventualVanishingHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}}

/-- One bound kills all positive cohomology of sufficiently large twists. -/
def EventualTwistVanishing (L M : X.Modules) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
    Subsingleton (ModuleH (tensor M (tensorPower L n)) (q + 1))

/-- Vanishing of the end terms kills middle cohomology. -/
theorem moduleH_subsingleton_middle (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : ℕ) [Subsingleton (ModuleH S.X₁ q)] [Subsingleton (ModuleH S.X₃ q)] :
    Subsingleton (ModuleH S.X₂ q) := by
  have hAb := CoherentDevissage.moduleToSheaf_shortExact hS
  have he : Function.Exact (moduleHMap S.f q) (moduleHMap S.g q) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₂' hAb q)
  have hz (x : ModuleH S.X₂ q) : x = 0 := by
    obtain ⟨y, hy⟩ := (he x).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

namespace EventualTwistVanishing
variable {L M N : X.Modules}

/-- Isomorphism transport for the coefficient sheaf. -/
theorem of_iso (e : M ≅ N) (h : EventualTwistVanishing L N) :
    EventualTwistVanishing L M := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, fun n hn q ↦ @moduleH_subsingleton_of_iso X _ _
    (ModuleSheafTensor.congr e (Iso.refl _)) (q + 1) (hd n hn q)⟩

/-- Retracts inherit a common bound for all positive cohomology groups. -/
theorem retract (i : M ⟶ N) (p : N ⟶ M) (hip : i ≫ p = 𝟙 M)
    (h : EventualTwistVanishing L N) : EventualTwistVanishing L M := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun n hn q ↦ ?_⟩
  let F := tensoring (tensorPower L n) ⋙ moduleRingHFunctor (RingHom.id Γ(X, ⊤)) (q + 1)
  have hi : Function.Injective (F.map i) := by
    apply Function.LeftInverse.injective (f := F.map i) (g := F.map p)
    intro x
    have hcomp : F.map i ≫ F.map p = 𝟙 (F.obj M) := by rw [← F.map_comp, hip, F.map_id]
    exact congr($(hcomp) x)
  let : Subsingleton (F.obj N) := hd n hn q
  exact hi.subsingleton

/-- An extension of two eventually vanishing coefficients eventually vanishes. -/
theorem middle (hL : LocallyFreeRankOne L) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : EventualTwistVanishing L S.X₁)
    (h₃ : EventualTwistVanishing L S.X₃) : EventualTwistVanishing L S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun n hn q ↦ ?_⟩
  exact @moduleH_subsingleton_middle X (S.map (tensoring (tensorPower L n)))
    (ModuleLineTensorExact.shortExact S hS _ (hL.tensorPower n)) (q + 1)
    (ha n ((le_max_left a b).trans hn) q) (hb n ((le_max_right a b).trans hn) q)

/-- A quotient eventually vanishes when its source and kernel eventually vanish. -/
theorem right (hL : LocallyFreeRankOne L) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : EventualTwistVanishing L S.X₁)
    (h₂ : EventualTwistVanishing L S.X₂) : EventualTwistVanishing L S.X₃ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  refine ⟨max a b, fun n hn q ↦ ?_⟩
  exact @moduleH_subsingleton_right X (S.map (tensoring (tensorPower L n)))
    (ModuleLineTensorExact.shortExact S hS _ (hL.tensorPower n)) (q + 1)
    (hb n ((le_max_right a b).trans hn) q) (ha n ((le_max_left a b).trans hn) (q + 1))

/-- Transfer across a map whose kernel and cokernel already satisfy vanishing. -/
theorem of_errors [IsLocallyNoetherian X] (hL : LocallyFreeRankOne L)
    [M.IsFinitePresentation] [N.IsFinitePresentation] (a : M ⟶ N)
    (hM : EventualTwistVanishing L M) (hk : EventualTwistVanishing L (kernel a))
    (hc : EventualTwistVanishing L (cokernel a)) : EventualTwistVanishing L N := by
  have hi : EventualTwistVanishing L (Abelian.image a) :=
    right hL (CoherentDevissage.coherentKernelImageComplex a)
      (CoherentDevissage.coherent_kernelImageSequence a).shortExact hk hM
  exact middle hL (ShortComplex.kernelSequence (cokernel.π a))
    (CoherentDevissage.coherent_imageCokernelSequence a).shortExact hi hc

end EventualTwistVanishing
end FLT.Mazur.FCurve
