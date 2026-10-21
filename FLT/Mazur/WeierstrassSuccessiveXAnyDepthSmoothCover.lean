/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueSmoothCover
public import FLT.Mazur.WeierstrassSuccessiveXZeroSmoothCover

/-!
# Smooth boundary coverage at every creation depth

The original incidence and horizontal functions cover the entire smooth chart,
including creation depth zero. This is the uniform criterion for pair transfers.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "F" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 F
local notation "c" => residue R b6
local notation "t" => tensorCoord W (π ^ k) π b3 b4 b6 F 0
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 F 2
variable {X : Scheme.{u}}
  (g : Spec (.of (ScalarExtension W (π ^ k) π b3 b4 b6 (ResidueField R))) ⟶ X)
  [IsOpenImmersion g] (p : X ⟶ Spec (.of (ResidueField R)))
  [LocallyOfFinitePresentation p]
  (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R)
    (ScalarExtension W (π ^ k) π b3 b4 b6 (ResidueField R)))))

include D hk h3 h4 hg in
/-- The two original boundary opens cover exactly the smooth part, also at depth zero. -/
theorem residueAnyDepth_mem_smooth_iff (z : Spec (.of T)) :
    g z ∈ p.smoothLocus ↔ t ∉ z.asIdeal ∨ v ∉ z.asIdeal := by
  by_cases hk0 : k = 0
  · exact zeroResidue_mem_smooth_iff D k hk0 hk b3 b4 b6 h3 h4 g p hg z
  · exact residueMiddle_mem_smooth_iff D k (Nat.pos_of_ne_zero hk0) hk
      b3 b4 b6 h3 h4 g p hg z

include D hk h3 h4 hg in
/-- A smooth point with vanishing abscissa belongs to the original incidence open. -/
theorem residueAnyDepth_incidence_nonzero (z : Spec (.of T))
    (hs : g z ∈ p.smoothLocus) (hz : v ∈ z.asIdeal) : t ∉ z.asIdeal := by
  have h := (residueAnyDepth_mem_smooth_iff D k hk b3 b4 b6 h3 h4 g p hg z).mp hs
  exact h.resolve_right (not_not.mpr hz)

end FLT.Mazur.WeierstrassSuccessiveX
