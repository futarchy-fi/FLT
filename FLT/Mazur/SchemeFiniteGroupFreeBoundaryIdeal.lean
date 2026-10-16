/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupFreeBoundary
public import FLT.Mazur.FiniteGroupFreeIdealDescent

/-!
# The full original equations of a free quotient boundary

The kernel of the original closed source restriction is stable under the
coordinate action. The constructed quotient boundary ideal extends to exactly
this original kernel. Thus the invariant lift construction retains the entire
closed structure, rather than only the underlying closed set.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
universe u
set_option backward.isDefEq.respectTransparency false
variable {G : Type u} [Group G] {X Y : Scheme.{u}}
  (ρ : G →* Aut X) (τ : G →* Aut Y) (i : X ⟶ Y)
  (hi : ∀ g : G, (ρ g).hom ≫ i = i ≫ (τ g).hom)

include hi

/-- The actual source ideal is stable under the coordinate action. -/
theorem boundaryKernel_stable (g : G) (a : Γ(Y, ⊤)) (ha : a ∈ RingHom.ker i.appTop.hom) :
    let _ := coordinateAction τ
    g • a ∈ RingHom.ker i.appTop.hom := by
  let _ := coordinateAction ρ
  let _ := coordinateAction τ
  change i.appTop.hom (g • a) = 0
  have h := congrArg (fun f : Γ(Y, ⊤) →+* Γ(X, ⊤) ↦ f a)
    (coordinateHom_comp ρ τ i hi g)
  change g • i.appTop.hom a = i.appTop.hom (g • a) at h
  rw [← h, RingHom.mem_ker.mp ha, smul_zero]

/-- The quotient boundary equations are exactly the invariant original source equations. -/
theorem invariantMap_ker :
    RingHom.ker (invariantMap ρ τ i hi) =
      (RingHom.ker i.appTop.hom).comap
        (let _ := coordinateAction τ; FiniteGroupQuotient.inclusion G Γ(Y, ⊤)) := by
  ext a
  change invariantMap ρ τ i hi a = 0 ↔ i.appTop.hom a.val = 0
  exact Subtype.ext_iff

variable [Finite G] [IsAffine Y]
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y) (g : G),
    a ≫ (τ g).hom = a → g = 1)
include hfree

/-- The quotient equations reconstruct the full original closed source ideal, with nilpotents. -/
theorem invariantMap_ker_extension :
    (RingHom.ker (invariantMap ρ τ i hi)).map
      (let _ := coordinateAction τ; FiniteGroupQuotient.inclusion G Γ(Y, ⊤)) =
        RingHom.ker i.appTop.hom := by
  let _ := coordinateAction τ
  rw [invariantMap_ker]
  exact FiniteGroupQuotient.invariantIdeal_map_comap_eq G (RingHom.ker i.appTop.hom)
    (boundaryKernel_stable ρ τ i hi) (coordinate_fixedPointIdeal_eq_top τ hfree)

end FLT.Mazur.SchemeFiniteGroupQuotient
