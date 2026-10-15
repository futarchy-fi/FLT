/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnvelopeBoundaryIdealSheaf

/-!
# Exact finite equations for whole closed-boundary tests

Vanishing of the pulled-back ideal, rather than nilpotence of its elements,
constructs a unique morphism into the actual closed boundary scheme. This
retains the whole source morphism, including all nilpotent information.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
variable {Y X T : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens) [IsAffine X]
  (s : Set Γ(X, ⊤)) (hs : Ideal.span s = denominatorIdeal π.appTop.hom O)
  [IsAffine T] (b : T ⟶ X)
local notation "I" => boundaryIdealSheaf π O
local notation "j" => Scheme.IdealSheafData.subschemeι I
include hs

/-- All original equations vanish exactly when the entire pulled-back ideal sheaf is zero. -/
theorem boundary_equations_zero_iff :
    Ideal.span (b.appTop.hom '' s) = ⊥ ↔ (I).comap b = ⊥ := by
  constructor
  · intro h
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_comap_top, boundaryIdealSheaf_top,
      ← hs, Ideal.map_span, h]
    rfl
  · intro h
    have he := congrArg (fun J : T.IdealSheafData ↦ J.ideal ⟨⊤, isAffineOpen_top T⟩) h
    simpa only [Scheme.IdealSheafData.ideal_comap_top, boundaryIdealSheaf_top,
      ← hs, Ideal.map_span, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using he

/-- Exact equation vanishing supplies the kernel containment for a closed scheme lift. -/
theorem boundary_equations_le_ker (h : Ideal.span (b.appTop.hom '' s) = ⊥) :
    (j).ker ≤ b.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot]
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
  exact le_bot_iff.mpr ((boundary_equations_zero_iff π O s hs b).mp h)

/-- Construct the full scheme lift from the original equations. -/
def boundaryEquationLift (h : Ideal.span (b.appTop.hom '' s) = ⊥) : T ⟶ (I).subscheme :=
  IsClosedImmersion.lift j b (boundary_equations_le_ker π O s hs b h)

/-- The lift retains the original whole test map. -/
@[reassoc]
theorem boundaryEquationLift_comp (h : Ideal.span (b.appTop.hom '' s) = ⊥) :
    boundaryEquationLift π O s hs b h ≫ j = b := IsClosedImmersion.lift_fac _ _ _

/-- The whole scheme lift is unique, including on nonreduced tests. -/
theorem boundaryEquationLift_unique (h : Ideal.span (b.appTop.hom '' s) = ⊥)
    (z : T ⟶ (I).subscheme) (hz : z ≫ j = b) :
    z = boundaryEquationLift π O s hs b h := by
  apply (cancel_mono j).mp
  rw [hz, boundaryEquationLift_comp]

/-- Finite equation vanishing is necessary as well as sufficient for closed factorization. -/
theorem boundary_equations_iff_exists_lift :
    Ideal.span (b.appTop.hom '' s) = ⊥ ↔ ∃ z : T ⟶ (I).subscheme, z ≫ j = b := by
  constructor
  · intro h
    exact ⟨boundaryEquationLift π O s hs b h, boundaryEquationLift_comp π O s hs b h⟩
  · rintro ⟨z, rfl⟩
    apply (boundary_equations_zero_iff π O s hs _).mpr
    apply le_bot_iff.mp
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    rw [Scheme.IdealSheafData.map_bot]
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using Scheme.Hom.le_ker_comp z j

end FLT.Mazur.SchemeOpenEnvelope
