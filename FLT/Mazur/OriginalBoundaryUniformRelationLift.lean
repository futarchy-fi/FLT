/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRelationOpenLift
public import FLT.Mazur.SchemeNoetherianUniformKernelPower

/-!
# A uniform original multiplier from a common solved relation open

Noetherianity of the original arrow scheme gives one scalar exponent for
all raw numerators whose two endpoints agree on the prescribed open. It
therefore gives simultaneous exact boundary lifts for arbitrary families
with such raw representatives, without finite generation of invariants.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsNoetherian D]
  (O : D.Opens) (s : compatibleFunctions p q)
  (hs : D.basicOpen (p.appTop s.val) ≤ O)

include hs in
/-- One original power makes every numerator satisfying the open equations fully invariant. -/
theorem exists_uniform_original_relation_multiplier :
    ∃ N : ℕ, ∀ a : Γ(A, ⊤),
      O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a) →
      s.val ^ N * a ∈ compatibleFunctions p q := by
  obtain ⟨N, hN⟩ := SchemeNoetherianUniformKernelPower.exists_uniform_power_eq
    O (p.appTop s.val) hs
  refine ⟨N, fun a ha ↦ ?_⟩
  change p.appTop (s.val ^ N * a) = q.appTop (s.val ^ N * a)
  rw [map_mul, map_mul, map_pow, map_pow, ← s.property]
  exact hN _ _ ha

include hs in
/-- The power is chosen before the boundary ideal or its section, on the full arrow scheme. -/
theorem exists_uniform_originalBoundary_relation_lift :
    ∃ N : ℕ, ∀ (J : A.IdealSheafData) (a : Γ(A, ⊤)),
      O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a) →
      s ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J (J.subschemeι.appTop a) := by
  obtain ⟨N, hN⟩ := exists_uniform_original_relation_multiplier O s hs
  refine ⟨N, fun J a ha ↦ ⟨⟨s.val ^ N * a, hN a ha⟩, ?_⟩⟩
  change J.subschemeι.appTop (s.val ^ N * a) =
    J.subschemeι.appTop (s ^ N).val * J.subschemeι.appTop a
  rw [map_mul]
  rfl

include hs in
/-- Arbitrarily many full boundary sections share one power when their raw lifts use one open. -/
theorem exists_uniform_originalBoundary_family_relation_lift
    (J : A.IdealSheafData) {ι : Type*} (t : ι → Γ(J.subscheme, ⊤))
    (hraw : ∀ i, ∃ a : Γ(A, ⊤), J.subschemeι.appTop a = t i ∧
      O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a)) :
    ∃ N : ℕ, ∀ i, s ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J (t i) := by
  obtain ⟨N, hN⟩ := exists_uniform_originalBoundary_relation_lift O s hs
  refine ⟨N, fun i ↦ ?_⟩
  obtain ⟨a, ha, he⟩ := hraw i
  simpa only [ha] using hN J a he

end FLT.Mazur.EquivalenceRelationOrderedFrames
