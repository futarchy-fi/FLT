# FC08 B18-SERRE-A: absolute and relative Serre vanishing

Checked 2026-09-30 against `ac3a862d`; this review is committed before code.
All caps below include headers and documentation, and are at most 450 lines.
Names in the blocked sketches are proposed interfaces, not existing declarations.
No vanishing, comparison isomorphism, or bound is to become a field of B17 data.

## Source review and scope

`ProjectiveCoherentCohomology` proves finiteness, not coherent Serre vanishing.
`ProjectiveTwistCechCohomologySumHomology.sheaf_isZero_homology_large`
proves positive Cech vanishing for O(d) when `-card ι < d`.
`ProjectiveTwistCohomology.twistModuleHEquiv` transfers it to actual ModuleH.
`exists_coherent_twist_presentation` supplies finite negative-twist quotients
with coherent kernels. `twistTensorEquivalence` makes twisting exact, and
`finiteAffineCover_moduleH_subsingleton` bounds cohomological dimension.
Together these suffice for absolute coherent Serre vanishing on main.

The B17 and B18 lane briefs were read in `../wt-r1e/BRIEF.md` and
`../wt-r5a/BRIEF.md`. Their pullback/relative-line and open-derived modules
remain owned by those lanes. This checkout has no `ModulePullback*.lean`.
The existing closed absolute cohomology comparison does not supply a tensor
projection formula or a relative higher-image vanishing theorem.

Rerun the evidence checks:

```
rg -n 'theorem|lemma|def ' FLT/Mazur/ProjectiveCoherentCohomology.lean
rg -n 'sheaf_isZero_homology_large|twistModuleHEquiv|exists_coherent_twist_presentation|twistTensorEquivalence' FLT/Mazur/Projective*.lean
rg -n 'ModulePushforwardAcyclic|moduleToSheaf_shortExact' FLT/Mazur/{AcyclicPushforwardCohomology,ModuleStalkExact}.lean
cat ../wt-r1e/BRIEF.md ../wt-r5a/BRIEF.md
```

## Main-only leaves, in implementation order

### 1. ModuleCohomologyVanishing (cap 160; main only)

```
moduleH_subsingleton_of_iso (e : M ≅ N) (q : ℕ)
  [Subsingleton (ModuleH N q)] : Subsingleton (ModuleH M q)
moduleH_subsingleton_coproduct (M : κ → X.Modules) [Finite κ] (q : ℕ)
  [∀ i, Subsingleton (ModuleH (M i) q)] : Subsingleton (ModuleH (∐ M) q)
moduleH_subsingleton_right (S : ShortComplex X.Modules) (hS : S.ShortExact) (q : ℕ)
  [Subsingleton (ModuleH S.X₂ q)] [Subsingleton (ModuleH S.X₁ (q+1))] :
  Subsingleton (ModuleH S.X₃ q)
```

Use `moduleRingHFunctor` with the identity scalar map, its additivity and
finite-coproduct preservation, `moduleToSheaf_shortExact`, and
`Sheaf.H.longSequence_exact₃'`. These are unconditional transport/exactness
lemmas for actual cohomology, without Noetherian assumptions.

### 2. ProjectiveTwistVanishing (cap 120; main + 1)

```
twist_moduleH_subsingleton [Fintype ι] (d : ℤ)
  (hd : -(Fintype.card ι : ℤ) < d) (q : ℕ) :
  Subsingleton (ModuleH (twistingSheaf R ι d) (q+1))
twist_moduleH_subsingleton_nonneg [Finite ι] (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
  Subsingleton (ModuleH (twistingSheaf R ι d) (q+1))
```

Use the Cech theorem and `twistModuleHEquiv`; handle an empty chart index
separately by `emptyAffineCover_moduleH_subsingleton`. No nonempty base,
nonempty index, or field assumption. Nonnegative twists include O(0).

### 3. ProjectiveTwistedPresentation (cap 180; main + 1-2)

```
twistTensor_shortExact (S : ShortComplex (space R ι).Modules)
  (hS : S.ShortExact) (n : ℤ) : (S.map (twistTensorFunctor R ι n)).ShortExact
twistTensor_twistSum_moduleH_subsingleton [Finite ι] [Finite κ]
  (a n : ℤ) (h : 0 ≤ a+n) (q : ℕ) :
  Subsingleton (ModuleH (twistTensor R ι
    (∐ fun _ : κ ↦ twistingSheaf R ι a) n) (q+1))
```

Use `twistTensorEquivalence`, `ShortExact.map_of_exact`,
`PreservesCoproduct.iso`, `twistingSheafTensorIso`, and leaves 1-2.
No chosen resolutions or assumed exactness of tensoring.

### 4. ProjectiveSerreVanishing (cap 240; main + 1-3)

```
exists_twistTensor_moduleH_subsingleton [IsNoetherianRing R] [Finite ι]
  (F : (space R ι).Modules) [F.IsFinitePresentation] :
  ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
    Subsingleton (ModuleH (twistTensor R ι F (n : ℤ)) (q+1))
```

Prove the stronger induction: for each k and coherent F there is a bound
working simultaneously for every positive q with `card ι ≤ q+k`.
At k=0 use the finite affine cover. At k+1 choose ONE coherent twist
presentation of F, use the induction bound for its kernel, and take its
maximum with the presentation degree. Leaves 1 and 3 give the long-exact
step. Finally take k=card ι. This provides ONE bound for all positive
cohomological degrees, not a separate bound in each degree.

### 7. ProjectiveSerrePresentationTower (cap 200; main + 3)

For any coherent F on polynomial projective space and any length c,
construct a finite tower of coherent negative-twist presentations. Output
its actual kernels, short exact sequences, finite summand indices and degrees.

```
coherentTwistPresentationTower (F) [F.IsFinitePresentation] (c : ℕ) :
  TwistPresentationTower R ι F c
```

Define the tower in this module using inductive constructors for the empty
tower and a coherent presentation followed by a tower of its kernel.
Use `exists_coherent_twist_presentation` repeatedly. This construction itself
is main-only and is implemented after leaf 4. Its application to the actual
B17 closed pushforward coefficient waits for B17-FINAL; that application
belongs to leaf 8. The structure stores no vanishing assumption.

## Leaves requiring the other lanes

### 5. ClosedLineProjectionFormula (cap 400; B17 pullback/tensor API)

For a closed immersion `i : Y ⟶ P`, a module F on Y and a locally free
rank-one L on P, construct the canonical isomorphism

```
pushforward i (tensor F (pullback i L)) ≅ tensor (pushforward i F) L
```

Use `ModuleSheafTensor.Bilinear`, its universal property, B17's actual
pullback and adjunction, and local rank-one trivializations. Prove the map
is an isomorphism on a trivializing open cover; use the existing underived
`closedPushforwardRestriction`. Include compatibility with open restriction.
Do not accept a projection-formula isomorphism as input. This is a new
module, not an edit to `ModulePullback*` or `RelativeVeryAmple*`.

### 6. ClosedProjectiveSerreVanishing (cap 180; 4-5 and B17 powers)

```
exists_closed_twist_moduleH_subsingleton (i : Y ⟶ space R ι)
  [IsClosedImmersion i] (F : Y.Modules) [F.IsFinitePresentation] :
  ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
    Subsingleton (ModuleH (tensor F (pullback i (twistingSheaf R ι n))) (q+1))
```

Use coherent closed pushforward, 4 applied to `i_* F`, 5, and
`closedPushforwardModuleHEquiv`.
For F=O_Y use B17's power-zero/unit and power-n coefficient identifications
to obtain the statement on its actual line powers. No relative conclusion yet.

### 8. RelativeSerreLocalizedTower (cap 450; 5,7, B17-FINAL)

On EVERY principal subopen D(r) of that affine base, transport the SAME
tower through flat base change, keeping its length and integer degrees.
Sketch: `localizeTower (T : TwistPresentationTower F c) (r : R) :
TwistPresentationTower (baseChangedCoefficient F r) c`.
Use exactness of restriction, the cartesian closed embedding, B17's
`ProjectiveTwistAffineBaseChange`, and the underived closed restriction
comparison. Establish closed coefficient base change and exactness here;
if those adapters exceed the cap, split before continuing. A new tower
chosen separately on each D(r) would not give a uniform bound.

### 9. RelativeSerreAffineVanishing (cap 240; 1-3,8, B17-FINAL)

```
∃ N : ℕ, ∀ n ≥ N, ∀ r : R, ∀ q : ℕ,
  Subsingleton (ModuleH ((power L n).restrict (pi ⁻¹ᵁ D(r)).ι) (q+1))
```

Take the maximum of the finite tower's degrees. Run the finite-cover/LES
induction of 4 on the transported tower, rather than choosing a new bound
for each r. Apply 5 and closed cohomology comparison on each D(r).
Use B17 coefficient comparisons for all powers including zero.

### 10. RelativeSerreAffineAcyclic (cap 300; 9, B18 5c-6a)

```
∃ N : ℕ, ∀ n ≥ N, ModulePushforwardAcyclic piAffine (power LAffine n)
```

Identify actual higher direct images with sheafification of open cohomology
using B18 6a and its module/abelian comparison. The principal opens form a
basis; 9 makes the cohomology presheaf zero on this basis, hence its
sheafification zero. Reflect zero through faithful module forgetting.
Crucially, vanishing on just the whole affine open is insufficient:
sections of a higher direct image are NOT the open cohomology presheaf.

### 11. RelativeSerreVanishing (cap 300; 10, B17-FINAL, B18 5c-6a)

For the actual B17 relative very ample presentation over a quasi-compact
Noetherian base, select a finite affine cover, take the maximum of the
bounds from 10, and use higher-image open restriction and local detection
of zero. Sketch:

```
relativeVeryAmple_eventually_acyclic (D : RelativeVeryAmplePresentation pi L) :
  ∃ N : ℕ, ∀ n ≥ N, ModulePushforwardAcyclic pi (power L n)
```

D contains the geometric closed embeddings and coefficient compatibility,
never a vanishing hypothesis. The precise B17 type name must be substituted
once its contract lands. Open restriction compatibility is proved by B18,
not added as a public theorem hypothesis. Quasi-compactness is necessary
for a single global bound and follows for the specified Chow base.

### 12. ChowSimultaneousSerreVanishing (cap 160; 11, B17-FINAL)

For B17's actual common line sheaf and its two relative presentations:

```
∃ N : ℕ, ∀ n ≥ N,
  ModulePushforwardAcyclic pi (power L n) ∧
  ModulePushforwardAcyclic g' (power L n)
```

Apply 11 twice and take the maximum. Export the existential single-n
specialization as well. This completes the geometric input to row 8;
B18 6b remains necessary for row 8's relative comparison application,
but not for this maximum-of-bounds step.

## Validation and boundaries

Build each main-only module in the foreground, then run exactly
`lake exe runLinter FLT.Mazur.<Module>` for that module. Add each to FLT.lean
in sorted order and commit locally after green checks. Check exported
axioms, source caps and import coverage. Never run the whole-library linter.
Leaves 1-4 and 7 are the ready work for this task. Leaves 5-6 and 8-12 require the actual
B17/B18 contracts above; they are not implemented by assuming those results.

Review refinement during execution: leaf 7's finite presentation tower does
not require B17 merely to construct it. Its geometric specialization does.
It is therefore included in the main-only work, avoiding an artificial
upstream dependency. The ready order is 1, 2, 3, 4, 7.

## Implemented main-only leaves

| Leaf | Module | Lines / cap | Local commit |
| --- | --- | --- | --- |
| 1 | `ModuleCohomologyVanishing` | 67 / 160 | `94d1f200` |
| 2 | `ProjectiveTwistVanishing` | 54 / 120 | `bc2f5cd4` |
| 3 | `ProjectiveTwistedPresentation` | 52 / 180 | `0d14d2e9` |
| 4 | `ProjectiveSerreVanishing` | 73 / 240 | `84afecdf` |
| 7 | `ProjectiveSerrePresentationTower` | 65 / 200 | `79b09420` |

The initial split was committed as `143caaba` before implementation;
`9070821a` removed leaf 7's artificial upstream dependency.
Each listed module passed both foreground commands, separately:

```
lake build FLT.Mazur.<Module>
lake exe runLinter FLT.Mazur.<Module>
```

The final sources compile without warnings and all five module linters
pass. A source scan checked the line caps, maximum width <=100, and absence
of admitted proofs/new axioms. `FLT.lean` has 1266 sorted imports, exactly
matching all source modules under FLT. No B17/B18-owned source was edited.

`lake env lean /tmp/serre-a-axioms.lean` exited 0. Its 12 exported-definition
checks returned only `propext`, `Classical.choice`, and `Quot.sound`:

* FCurve: `moduleH_subsingleton_of_iso`, `moduleH_subsingleton_coproduct`,
  `moduleH_subsingleton_right`.
* ProjectiveSpace: `twist_moduleH_subsingleton`,
  `twist_moduleH_subsingleton_nonneg`, `twistTensor_shortExact`,
  `twistTensorTwistSumIso`, `twistTensor_twistSum_moduleH_subsingleton`,
  `exists_twistTensor_moduleH_subsingleton`, `nonempty_twistPresentationTower`,
  `coherentTwistPresentationTower`, `TwistPresentationTower.bound`.

All names have the prefix `FLT.Mazur.`. The probe imports
`ProjectiveSerreVanishing` and `ProjectiveSerrePresentationTower`.
The full relative endpoint and simultaneous Chow acyclicity are NOT proved;
leaves 5-6 and 8-12 have the exact prerequisites recorded in `BLOCKED.md`.

Final check at **2026-09-30 08:27 UTC**:

* The five per-module builds, five per-module lint runs, and 12 axiom checks
  above exited 0. These satisfy the brief's main-only completion criterion.
* The additional `lake build +FLT:olean` check reached compilation of
  `FLT.lean`, but was deliberately terminated after that compiler had run
  for over 11 minutes without diagnostics under host I/O pressure. The
  shell exited 143. **The root build is incomplete, not verified green.**
  Log: `/tmp/serre-a-root-build.log`; the terminated build processes were
  confirmed absent with `ps -p 1336204,1296261 -o pid,stat,args`.
* All build and lint commands ran in the foreground, sequentially. No
  library-wide lint was run. The sorted exact root-import coverage check
  passed independently; it does not substitute for a completed root build.
* `git diff --check` passed. Inherited untracked briefs were preserved.
  Nothing was pushed; no B17/B18-owned source module was changed.

Next implementation boundary: leaf 5 after B17's actual pullback/tensor
contract lands; then leaf 6 and the uniformly localized tower in leaf 8.
The B18 5c-6a contracts are additionally needed for leaves 10-11. No user
policy decision is needed to resume at those technical boundaries.
