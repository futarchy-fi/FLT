/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryHomCoordinates
public import FLT.GaloisRepresentation.Extensions.LiftCocycle

/-!
# Exact two-line filtrations of representations

An injection and a quotient describe the actual representation. Applying
Hom from the quotient character makes a linear section invariant modulo
the Hom coefficient submodule. No extension class is supplied as input.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.Extensions

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]

/-- An exact extension of the beta character line by the alpha character line. -/
structure OrdinaryFiltration (ρ : Representation k G V) (α β : G →* kˣ) where
  /-- The chosen sub-line inside the middle representation. -/
  injection : k →ₗ[k] V
  /-- The quotient-line coordinate map. -/
  projection : V →ₗ[k] k
  injective : Function.Injective injection
  surjective : Function.Surjective projection
  exact : LinearMap.ker projection = LinearMap.range injection
  injection_equivariant : ∀ g x, ρ g (injection x) = injection ((α g : k) * x)
  projection_equivariant : ∀ g x, projection (ρ g x) = (β g : k) * projection x

/-- Hom from the quotient character into the middle representation. -/
def OrdinarySectionModule (_ρ : Representation k G V) (_β : G →* kˣ) := k →ₗ[k] V

variable (ρ : Representation k G V) (α β : G →* kˣ)

instance : AddCommGroup (OrdinarySectionModule ρ β) := inferInstanceAs (AddCommGroup (k →ₗ[k] V))
instance : TopologicalSpace (OrdinarySectionModule ρ β) := ⊥
instance : DiscreteTopology (OrdinarySectionModule ρ β) := ⟨rfl⟩

instance : DistribMulAction G (OrdinarySectionModule ρ β) where
  smul g f := Representation.linHom (characterLine β) ρ g f
  one_smul f := by
    change Representation.linHom (characterLine β) ρ 1 f = f
    rw [map_one]; rfl
  mul_smul g h f := by
    change Representation.linHom (characterLine β) ρ (g * h) f = _
    rw [map_mul]; rfl
  smul_zero g := map_zero _
  smul_add g f h := map_add _ _ _

namespace OrdinaryFiltration

variable {ρ α β} (E : OrdinaryFiltration ρ α β)

/-- Postcomposition embeds actual Hom coefficients into the section module. -/
def homInjection : OrdinaryHomModule α β →+ OrdinarySectionModule ρ β where
  toFun f := E.injection.comp f
  map_zero' := by
    change E.injection.comp 0 = 0
    simp
  map_add' f h := by
    dsimp [OrdinaryHomModule] at f h
    apply LinearMap.ext
    intro x
    exact E.injection.map_add (f x) (h x)

/-- Exactness on coefficients begins with this injective map. -/
theorem homInjection_injective : Function.Injective E.homInjection := by
  intro f h he
  apply LinearMap.ext
  intro x
  exact E.injective (congrArg (fun t : k →ₗ[k] V ↦ t x) he)

/-- Postcomposition respects the actual Hom actions. -/
theorem homInjection_equivariant (g : G) (f : OrdinaryHomModule α β) :
    E.homInjection (g • f) = g • E.homInjection f := by
  dsimp [OrdinaryHomModule] at f
  apply LinearMap.ext
  intro x
  exact (E.injection_equivariant g (f (((β g⁻¹ : kˣ) : k) * x))).symm

/-- A vector above one defines a linear section of the quotient. -/
def sectionOf (_E : OrdinaryFiltration ρ α β) (w : V) : OrdinarySectionModule ρ β :=
  LinearMap.toSpanSingleton k V w

/-- The difference of a translated section lies in the actual Hom submodule. -/
theorem section_difference_range (w : V) (hw : E.projection w = 1) (g : G) :
    g • E.sectionOf w - E.sectionOf w ∈ E.homInjection.range := by
  have hz : E.projection ((show k →ₗ[k] V from g • E.sectionOf w - E.sectionOf w) 1) = 0 := by
    change E.projection
      (ρ g (((↑(β g⁻¹) : k) * 1) • w) - (1 : k) • w) = 0
    simp only [mul_one, one_smul]
    rw [map_sub, E.projection_equivariant, map_smul, hw]
    simp
  have hm : (show k →ₗ[k] V from g • E.sectionOf w - E.sectionOf w) 1 ∈
      LinearMap.range E.injection := by
    rw [← E.exact]
    exact hz
  obtain ⟨a, ha⟩ := hm
  refine ⟨LinearMap.toSpanSingleton k k a, ?_⟩
  apply LinearMap.ext_ring
  change E.injection ((1 : k) • a) = _
  simpa only [one_smul] using ha

/-- Two sections above one differ by a unique coefficient map. -/
theorem section_difference (w z : V) (hw : E.projection w = 1)
    (hz : E.projection z = 1) : ∃ a : OrdinaryHomModule α β,
      E.sectionOf z = E.sectionOf w + E.homInjection a := by
  have hm : z - w ∈ LinearMap.range E.injection := by
    rw [← E.exact]
    change E.projection (z - w) = 0
    rw [map_sub, hz, hw, sub_self]
  obtain ⟨a, ha⟩ := hm
  refine ⟨LinearMap.toSpanSingleton k k a, ?_⟩
  apply LinearMap.ext_ring
  change (1 : k) • z = (1 : k) • w + E.injection ((1 : k) • a)
  simp only [one_smul]
  rw [ha]
  abel

end OrdinaryFiltration

end GaloisRepresentation.Extensions
