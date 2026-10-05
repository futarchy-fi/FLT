/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleConverse
public import FLT.Mazur.ClosedProjectiveSerreVanishing
public import FLT.Mazur.TensorPowerReassociation

/-!
# Serre vanishing for an ample line on a proper scheme

A positive power has a closed projective presentation. Apply projective
Serre vanishing to the finitely many residual twists, then write each large
exponent as its remainder plus a multiple of that power. One bound works for
all positive cohomological degrees and for every sufficiently large exponent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback ProjectiveSpace

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of R))

/-- A very ample presentation gives Serre vanishing with any coherent coefficient. -/
theorem veryAmplePresentation_coherent_vanishing {L : X.Modules}
    (p : VeryAmplePresentation f L) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensor M (tensorPower L n)) (q + 1)) := by
  obtain ⟨N, hN⟩ := exists_closed_twist_moduleH_subsingleton R
    (Fin (p.dimension + 1)) p.embedding M
  refine ⟨N, fun n hn q ↦ ?_⟩
  let e : tensorPower L n ≅ (pullback p.embedding).obj (O R p.dimension (n : ℤ)) :=
    tensorPowerCongr p.coefficientIso n ≪≫ pullbackOOnePowerIso p.embedding n
  exact @moduleH_subsingleton_of_iso X _ _ (ModuleSheafTensor.congr (Iso.refl M) e)
    (q + 1) (hN n hn q)

/-- Coherent twists by an ample line eventually have no positive cohomology. -/
theorem AmpleLineBundle.coherent_vanishing [IsProper f] {L : X.Modules}
    (hL : AmpleLineBundle L) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensor M (tensorPower L n)) (q + 1)) := by
  classical
  obtain ⟨m, hm, ⟨p⟩⟩ := hL.exists_power_presentation f
  have hv (r : Fin m) : ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensor (tensor M (tensorPower L r.val))
        (tensorPower (tensorPower L m) n)) (q + 1)) := by
    have := tensor_line_isFinitePresentation M (tensorPower L r.val) (hL.2.1.tensorPower r.val)
    exact veryAmplePresentation_coherent_vanishing f p (tensor M (tensorPower L r.val))
  choose B hB using hv
  let N := Finset.univ.sup B
  refine ⟨m * N, fun n hn q ↦ ?_⟩
  let r : Fin m := ⟨n % m, Nat.mod_lt n hm⟩
  have hbound : B r ≤ n / m := by
    apply le_trans (Finset.le_sup (f := B) (Finset.mem_univ r))
    exact (Nat.le_div_iff_mul_le hm).mpr (by simpa only [Nat.mul_comm] using hn)
  have hz := hB r (n / m) hbound q
  let e : tensor (tensor M (tensorPower L r.val))
      (tensorPower (tensorPower L m) (n / m)) ≅ tensor M (tensorPower L n) :=
    ModuleSheafTensorAssociator.associator _ _ _ ≪≫
      ModuleSheafTensor.congr (Iso.refl M)
        (ModuleSheafTensor.congr (Iso.refl _) (tensorPowerMulIso L m (n / m)) ≪≫
          tensorPowerAddIso L r.val (m * (n / m)) ≪≫
            eqToIso (congrArg (tensorPower L) (Nat.mod_add_div n m)))
  exact @moduleH_subsingleton_of_iso X _ _ e.symm (q + 1) hz

end FLT.Mazur.FCurve
