/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAugmentationDecomposition

/-!
# Character functions on a one-dimensional generic point space

Nonzero points form one scalar orbit. The ratio of two equivariant functions
with the same character is Galois fixed and therefore lies in the generic
base field. This proves proportionality without assuming character ranks.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
namespace CharacterRank

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Nonzero vectors of a one-dimensional space form a single scalar-unit orbit. -/
theorem scalar_orbit (hdim : Module.finrank F V = 1) (v w : V)
    (hv : v ≠ 0) (hw : w ≠ 0) : ∃ a : Fˣ, (a : F) • v = w := by
  let e := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some.symm
  have hv' : e v ≠ 0 := e.map_ne_zero_iff.mpr hv
  have hw' : e w ≠ 0 := e.map_ne_zero_iff.mpr hw
  refine ⟨Units.mk0 (e w / e v) (div_ne_zero hw' hv'), ?_⟩
  apply e.injective
  simp [hv']

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [DistribMulAction (L ≃ₐ[K] L) V]

/-- The ratio of two character functions is fixed by the generic Galois group. -/
theorem ratio_fixed (hdim : Module.finrank F V = 1) (χ : Fˣ →* Kˣ)
    (v : V) (hv : v ≠ 0) (f g : V →[L ≃ₐ[K] L] L)
    (hf : ∀ (a : Fˣ) x, f ((a : F) • x) = algebraMap K L (χ a) * f x)
    (hg : ∀ (a : Fˣ) x, g ((a : F) • x) = algebraMap K L (χ a) * g x) :
    ∃ c : K, algebraMap K L c = g v / f v := by
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  have hs (u : V →[L ≃ₐ[K] L] L) : σ (u v) = u (σ • v) := by
    simpa only [AlgEquiv.smul_def] using (map_smul u σ v).symm
  have hvσ : σ • v ≠ 0 := fun h ↦ hv (by simpa using congrArg (σ⁻¹ • ·) h)
  obtain ⟨a, ha⟩ := scalar_orbit hdim v (σ • v) hv hvσ
  rw [map_div₀, hs g, hs f, ← ha, hg, hf, mul_div_mul_left]
  exact (map_ne_zero (algebraMap K L)).mpr (Units.ne_zero _)

/-- Equivariant augmentation functions of one character are proportional over K. -/
theorem proportional (hdim : Module.finrank F V = 1) (χ : Fˣ →* Kˣ)
    (f g : V →[L ≃ₐ[K] L] L) (hf : f ≠ 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfc : ∀ (a : Fˣ) x, f ((a : F) • x) = algebraMap K L (χ a) * f x)
    (hgc : ∀ (a : Fˣ) x, g ((a : F) • x) = algebraMap K L (χ a) * g x) :
    ∃ c : K, g = c • f := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra! h
    exact hf (by ext v; exact h v)
  have hv0 : v ≠ 0 := fun h ↦ hv (h ▸ hf0)
  obtain ⟨c, hc⟩ := ratio_fixed hdim χ v hv0 f g hfc hgc
  have hcv : g v = algebraMap K L c * f v := by rw [hc, div_mul_cancel₀ _ hv]
  refine ⟨c, ?_⟩
  ext w
  change g w = (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K V L w) (c • f)
  rw [map_smul, Algebra.smul_def]
  change g w = algebraMap K L c * f w
  by_cases hw : w = 0
  · simp [hw, hf0, hg0]
  · obtain ⟨a, rfl⟩ := scalar_orbit hdim v w hv0 hw
    rw [hfc, hgc, hcv]
    ring

end CharacterRank
end ThreeAdicPlan
