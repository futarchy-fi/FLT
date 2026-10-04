/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleExtension

/-!
# Representatives of the first two connecting maps

Short exactness constructs the lifts and the boundary cocycles. No splitting
of the coefficient modules is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G]
  (S : ShortComplex (Rep k G)) (hS : S.ShortExact)

include hS in
/-- Exactness provides a coefficient preimage of every element in the kernel. -/
theorem coefficient_kernel_preimage (y : S.X₂) (hy : S.g.hom y = 0) :
    ∃ x : S.X₁, S.f.hom x = y := by
  have h := (ShortComplex.exact_map_iff_of_faithful S
    (forget₂ (Rep k G) (ModuleCat k))).mpr hS.exact
  exact (ShortComplex.moduleCat_exact_iff _).mp h y hy

/-- A lifted invariant has a one-cocycle boundary, with the actual connecting class. -/
theorem boundary_one_representative (z : S.X₃.ρ.invariants)
    (x : S.X₂) (hx : S.g.hom x = z) :
    ∃ b : cocycles₁ S.X₁,
      S.f.hom ∘ b = d₀₁ S.X₂ x ∧
      groupCohomology.δ hS 0 1 rfl ((H0Iso S.X₃).inv z) = H1π S.X₁ b := by
  have h (g : G) : ∃ y : S.X₁, S.f.hom y = d₀₁ S.X₂ x g := by
    apply coefficient_kernel_preimage S hS
    change S.g.hom (S.X₂.ρ g x - x) = 0
    rw [map_sub, Rep.hom_comm_apply, hx, z.property, sub_self]
  choose b hb using h
  have he : S.f.hom ∘ b = d₀₁ S.X₂ x := funext hb
  exact ⟨⟨b, mem_cocycles₁_of_comp_eq_d₀₁ hS he⟩, he, δ₀_apply hS z x hx b he⟩

/-- A lifted one-cocycle has a two-cocycle boundary representing its connecting class. -/
theorem boundary_two_representative (b : cocycles₁ S.X₃) :
    ∃ (t : G → S.X₂) (c : cocycles₂ S.X₁),
      S.g.hom ∘ t = b ∧ S.f.hom ∘ c = d₁₂ S.X₂ t ∧
      groupCohomology.δ hS 1 2 rfl (H1π S.X₃ b) = H2π S.X₁ c := by
  have he := (Rep.epi_iff_surjective S.g).mp hS.epi_g
  choose t ht using fun g => he (b g)
  have h (v : G × G) : ∃ y : S.X₁, S.f.hom y = d₁₂ S.X₂ t v := by
    apply coefficient_kernel_preimage S hS
    change S.g.hom (S.X₂.ρ v.1 (t v.2) - t (v.1 * v.2) + t v.1) = 0
    rw [map_add, map_sub, Rep.hom_comm_apply, ht, ht, ht]
    exact congrFun (cocycles₁.d₁₂_apply b) v
  choose c hc using h
  have hd : S.f.hom ∘ c = d₁₂ S.X₂ t := funext hc
  exact ⟨t, ⟨c, mem_cocycles₂_of_comp_eq_d₁₂ hS hd⟩,
    funext ht, hd, δ₁_apply hS b t (funext ht) c hd⟩

end LocalClassFieldTheory
