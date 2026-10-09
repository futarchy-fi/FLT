/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFlatCokernel
public import FLT.Mazur.RelativeSums

/-!
# Descending flatness through a bounded complex

For consecutive differentials, the previous cokernel is an extension of
homology by the next image. Flat homology, a flat next term and a flat next
cokernel therefore imply flatness of the previous cokernel. This is the
induction step for universal kernel base change on bounded flat complexes.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FlatCokernelStep

universe u
variable {R M N P : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (d : M →ₗ[R] N) (e : N →ₗ[R] P)

/-- The canonical injection of explicit homology into the incoming cokernel. -/
def homologyInclusion : (e.ker ⧸ d.range.comap e.ker.subtype) →ₗ[R] N ⧸ d.range :=
  (d.range.comap e.ker.subtype).liftQ (d.range.mkQ.comp e.ker.subtype) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero d.range).mpr hx)

/-- The homology-to-cokernel map is injective. -/
theorem homologyInclusion_injective : Function.Injective (homologyInclusion d e) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero d.range).mp hx

/-- The induced surjection from the incoming cokernel to the outgoing image. -/
def cokernelToRange (h : e.comp d = 0) : (N ⧸ d.range) →ₗ[R] e.range :=
  d.range.liftQ e.rangeRestrict (by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    exact LinearMap.congr_fun h x)

/-- Quotienting the source leaves the outgoing image unchanged. -/
theorem cokernelToRange_surjective (h : e.comp d = 0) :
    Function.Surjective (cokernelToRange d e h) := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective_rangeRestrict y
  exact ⟨d.range.mkQ x, rfl⟩

/-- The incoming cokernel is an extension of the next image by actual homology. -/
theorem homology_cokernel_exact (h : e.comp d = 0) :
    Function.Exact (homologyInclusion d e) (cokernelToRange d e h) := by
  intro z
  obtain ⟨x, rfl⟩ := d.range.mkQ_surjective z
  constructor
  · intro hx
    have hx0 : e x = 0 := congrArg Subtype.val hx
    exact ⟨(d.range.comap e.ker.subtype).mkQ ⟨x, hx0⟩, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := (d.range.comap e.ker.subtype).mkQ_surjective y
    rw [← hy]
    apply Subtype.ext
    exact y.property

/-- Flat homology and flat outgoing cokernel propagate flatness one degree downward. -/
theorem cokernel_flat_of_homology_flat (h : e.comp d = 0)
    [Module.Flat R P] [Module.Flat R (P ⧸ e.range)]
    [Module.Flat R (e.ker ⧸ d.range.comap e.ker.subtype)] :
    Module.Flat R (N ⧸ d.range) := by
  let _ := TensorKernelFlatCokernel.range_flat e
  exact FCurve.flat_of_shortExact (homologyInclusion d e) (cokernelToRange d e h)
    (homologyInclusion_injective d e) (cokernelToRange_surjective d e h)
    (homology_cokernel_exact d e h)

section Bounded

variable {A : Type u} [CommRing A] (C : ℕ → Type u)
  [∀ n, AddCommGroup (C n)] [∀ n, Module A (C n)] [∀ n, Module.Flat A (C n)]
  (dC : ∀ n, C n →ₗ[A] C (n + 1))
  (hdd : ∀ n, (dC (n + 1)).comp (dC n) = 0)
  (hH : ∀ n, Module.Flat A
    ((dC (n + 1)).ker ⧸ (dC n).range.comap (dC (n + 1)).ker.subtype))
  (b : ℕ) (hb : ∀ n, b ≤ n → Subsingleton (C n))

include hdd hH hb in
/-- Bounded flat complexes with flat positive cohomology have flat differential cokernels. -/
theorem bounded_cokernel_flat (n : ℕ) : Module.Flat A (C (n + 1) ⧸ (dC n).range) := by
  suffices ∀ k n, b ≤ n + k → Module.Flat A (C (n + 1) ⧸ (dC n).range) from
    this b n (by omega)
  intro k
  induction k with
  | zero =>
    intro n hn
    let _ := hb (n + 1) (by omega)
    infer_instance
  | succ k ih =>
    intro n hn
    let _ := ih (n + 1) (by omega)
    let _ := hH n
    exact cokernel_flat_of_homology_flat (dC n) (dC (n + 1)) (hdd n)

include hdd hH hb in
/-- Every kernel in such a bounded complex commutes with arbitrary tensor coefficients. -/
theorem bounded_tensorKer_bijective (n : ℕ) (B : Type*) [AddCommGroup B] [Module A B] :
    Function.Bijective (LinearMap.tensorKer A B (dC n)) := by
  let _ := bounded_cokernel_flat C dC hdd hH b hb n
  exact TensorKernelFlatCokernel.tensorKer_bijective (dC n) B

end Bounded
end FLT.Mazur.FlatCokernelStep
