/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteCharacterInertia
public import FLT.AbsoluteGaloisGroup.WildInertiaProP

/-!
# Cyclic prime-to-characteristic quotients defined only on inertia

An open kernel on inertia contains a finite-level restriction kernel.
The finite DVR inertia theorem then proves cyclicity, without requiring
the character to extend to the whole local Galois group.
-/

@[expose] public noncomputable section
namespace LocalRamification
open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Γ" => Field.absoluteGaloisGroup (v.adicCompletion K)

/-- An open inertia kernel contains an actual finite Galois restriction kernel. -/
theorem exists_finiteIdealInertiaRestriction_ker_le
    {H : Type*} [Group H] (f : localInertiaGroup v →* H)
    (hf : IsOpen (f.ker : Set (localInertiaGroup v))) :
    ∃ N : OpenNormalSubgroup Γ, (finiteIdealInertiaRestriction v N).ker ≤ f.ker := by
  obtain ⟨U, hU, he⟩ := isOpen_induced_iff.mp hf
  have h1 : (1 : Γ) ∈ U := by
    have h : (1 : localInertiaGroup v) ∈ (f.ker : Set _) := f.ker.one_mem
    rw [← he] at h
    exact h
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  refine ⟨N, fun σ hσ ↦ ?_⟩
  rw [← SetLike.mem_coe, ← he]
  apply hN
  apply (finiteRestriction_eq_one_iff v N σ).mp
  exact congrArg Subtype.val (show finiteIdealInertiaRestriction v N σ = 1 from hσ)

attribute [local instance] finiteLevel_finiteDimensional

set_option maxHeartbeats 1000000 in
-- The finite Galois integral-closure instances need additional elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
/-- Every finite prime-to-p quotient of inertia with open kernel is cyclic. -/
theorem isCyclic_inertia_quotient_of_coprime {p : ℕ} (hp : p.Prime)
    [CharP (ResidueField (v.adicCompletionIntegers K)) p]
    {H : Type*} [Group H] [Finite H] (f : localInertiaGroup v →* H)
    (hf : IsOpen (f.ker : Set (localInertiaGroup v)))
    (hs : Function.Surjective f) (hc : p.Coprime (Nat.card H)) : IsCyclic H := by
  obtain ⟨N, hN⟩ := exists_finiteIdealInertiaRestriction_ker_le v f hf
  let t := finiteIdealInertiaRestriction v N
  have ht := finiteIdealInertiaRestriction_surjective v N
  let f' := t.liftOfSurjective ht ⟨f, hN⟩
  have he (g : localInertiaGroup v) : f' (t g) = f g := by simp [f']
  have hs' : Function.Surjective f' := by
    intro y
    obtain ⟨g, rfl⟩ := hs y
    exact ⟨t g, he g⟩
  exact ThreeAdicPlan.isCyclic_finiteLocalInertia_quotient v
    (IntermediateField.fixedField N.toSubgroup) hp hc f' hs'

/-- A finite prime-to-p target gives a cyclic actual inertia image. -/
theorem isCyclic_inertia_range_of_coprime {p : ℕ} (hp : p.Prime)
    [CharP (ResidueField (v.adicCompletionIntegers K)) p]
    {H : Type*} [Group H] [Finite H] (f : localInertiaGroup v →* H)
    (hf : IsOpen (f.ker : Set (localInertiaGroup v)))
    (hc : p.Coprime (Nat.card H)) : IsCyclic f.range := by
  apply isCyclic_inertia_quotient_of_coprime v hp f.rangeRestrict
    (by simpa only [MonoidHom.ker_rangeRestrict] using hf) f.rangeRestrict_surjective
  exact hc.of_dvd_right (Subgroup.card_subgroup_dvd_card _)

end LocalRamification
