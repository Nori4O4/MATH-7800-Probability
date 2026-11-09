/-
  Math 7800 (Fall 2026) -- Take-home Lean midterm, Project A.
  Scaffold release: 2026-10-13. Due: Thursday, 2026-10-29, Gradescope.

  Read Midterm/README.md before starting.
  Replace ALL five `sorry` placeholders with proofs (four lemmas and
  the main theorem). None may remain in a final submission.
  Keep the definitions, namespace, and five statements unchanged.
  Add helper lemmas as needed. General Mathlib set algebra is allowed.
  Do not use MeasurableSpace.DynkinSystem.*, any constant beginning
  MeasurableSpace.generateFrom, or MeasurableSpace.induction_on_inter,
  including through a helper lemma. See README.md for the proof map.
  Check the two projects separately: they share the frozen definitions.
-/
import Mathlib

open Set Function

namespace Math7800.Midterm

variable {Ω : Type*}

-- BEGIN FROZEN DEFINITIONS
/-- π-system: closed under finite intersection. (∅ allowed, as in Mathlib.) -/
def IsPiSys (P : Set (Set Ω)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ∩ B ∈ P

/-- λ-system (Billingsley): contains Ω, closed under complements and
countable disjoint unions. -/
structure IsLambdaSys (L : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ L
  compl_mem : ∀ A ∈ L, Aᶜ ∈ L
  iUnion_mem : ∀ f : ℕ → Set Ω, Pairwise (Disjoint on f) → (∀ n, f n ∈ L) →
    (⋃ n, f n) ∈ L

structure IsSigmaField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  iUnion_mem : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ F) → (⋃ n, f n) ∈ F

/-- Field (algebra) of sets. -/
structure IsField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- Monotone class: closed under increasing unions and decreasing
intersections of sequences. -/
structure IsMonotoneClass (M : Set (Set Ω)) : Prop where
  iUnion_mem : ∀ f : ℕ → Set Ω, Monotone f → (∀ n, f n ∈ M) → (⋃ n, f n) ∈ M
  iInter_mem : ∀ f : ℕ → Set Ω, Antitone f → (∀ n, f n ∈ M) → (⋂ n, f n) ∈ M

def sigmaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {F | IsSigmaField F ∧ A ⊆ F}
def lambdaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {L | IsLambdaSys L ∧ A ⊆ L}
def monoGen (A : Set (Set Ω)) : Set (Set Ω) :=
  ⋂₀ {M | IsMonotoneClass M ∧ A ⊆ M}
-- END FROZEN DEFINITIONS

--1st Lemma
-- Want to show what everything in lambdaGen A satisfies univ_mem, compl_mem and iUonion_mem
lemma lambdaGen_isLambdaSys (A : Set (Set Ω)) : IsLambdaSys (lambdaGen A) := by
  unfold lambdaGen-- Replace lambdaGen A by the definition
  refine ⟨?_, ?_, ?_⟩ -- Break the proof into 3 parts
  · -- Goal: univ ∈ ⋂₀ {L | IsLambdaSys L ∧ A ⊆ L}
    -- Being in an intersection means being in every L of the family
    rw [Set.mem_sInter]
    -- So take any such L; hL says "L is a λ-system and A ⊆ L"
    intro L hL -- Introduct a new hypothesis
    -- Every λ-system contains Ω
    exact hL.1.univ_mem

  · intro s hs
    rw [Set.mem_sInter]
    intro L hL
    --use the compl_mem to show this is true for s and things in the parentheses shows s is in every L
    exact hL.1.compl_mem s (Set.mem_sInter.mp hs L hL)

  · intro f dj hf
    apply Set.mem_sInter.mpr
    intro L hLA
    --The parentheses contain a function that supplies a proof for each index i
    exact hLA.1.iUnion_mem f dj (fun i => Set.mem_sInter.mp (hf i) L hLA)

--2nd Lemma
lemma subset_lambdaGen (A : Set (Set Ω)) : A ⊆ lambdaGen A := by
  unfold lambdaGen
  intro s hs
  -- Same as saying if we can prove this, we can prove the goal
  apply Set.mem_sInter.mpr
  intro L hLA
  exact hLA.2 hs

--3rd Lemma
/-- ∅ = univᶜ is in every λ-system. -/
lemma IsLambdaSys.empty_mem {L : Set (Set Ω)} (hL : IsLambdaSys L) : ∅ ∈ L := by
  have h := hL.compl_mem univ hL.univ_mem
  rwa [compl_univ] at h -- rewrite the assumption

--4th Lemma
/-- Disjoint union of two sets, using the sequence X, Y, ∅, ∅, ... -/
lemma IsLambdaSys.union_mem {L : Set (Set Ω)} (hL : IsLambdaSys L) {X Y : Set Ω}
    (hX : X ∈ L) (hY : Y ∈ L) (hXY : Disjoint X Y) : X ∪ Y ∈ L := by
  let f : ℕ → Set Ω := fun n => if n = 0 then X else if n = 1 then Y else ∅
  -- the union of the sequence is X ∪ Y
  have hU : (⋃ n, f n) = X ∪ Y := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hn⟩
      simp only [f] at hn
      split_ifs at hn
      · exact Or.inl hn
      · exact Or.inr hn
      · simp at hn
    · rintro (hx | hx)
      · exact ⟨0, by simp [f, hx]⟩
      · exact ⟨1, by simp [f, hx]⟩
  rw [← hU]
  apply hL.iUnion_mem f
  · -- pairwise disjoint: check every case of i and j
    intro i j hij
    simp only [Function.onFun, f]
    split_ifs <;> first
      | exact absurd (by omega : i = j) hij
      | exact hXY
      | exact hXY.symm
      | simp
  · -- every term is in L
    intro n
    simp only [f]
    split_ifs
    · exact hX
    · exact hY
    · exact hL.empty_mem

--5th Lemma
/-- Proper difference: Y ⊆ X, both in L ⟹ X \ Y ∈ L. -/
lemma IsLambdaSys.diff_mem {L : Set (Set Ω)} (hL : IsLambdaSys L) {X Y : Set Ω}
    (hX : X ∈ L) (hY : Y ∈ L) (hYX : Y ⊆ X) : X \ Y ∈ L := by
  -- X \ Y = (Xᶜ ∪ Y)ᶜ
  have h : X \ Y = (Xᶜ ∪ Y)ᶜ := by
    ext x
    simp only [mem_sdiff, mem_compl_iff, mem_union]
    tauto
  rw [h]
  apply hL.compl_mem
  apply hL.union_mem (hL.compl_mem X hX) hY
  -- Xᶜ and Y are disjoint because Y ⊆ X  -- Xᶜ and Y are disjoint because Y ⊆ X
  unfold Disjoint
  intro Z hZX hZY x hx
  -- x ∈ Z gives x ∈ Y ⊆ X, but also x ∈ Xᶜ: contradiction
  exact absurd (hYX (hZY hx)) (hZX hx)

--6th Lemma
/-- Key fact: if C ∈ L, then {B | C ∩ B ∈ L} is a λ-system. -/
lemma isLambdaSys_inter_slice {L : Set (Set Ω)} (hL : IsLambdaSys L) {C : Set Ω}
    (hC : C ∈ L) : IsLambdaSys {B | C ∩ B ∈ L} := by
  refine ⟨?_, ?_, ?_⟩
  · -- C ∩ Ω = C
    show C ∩ univ ∈ L
    rw [inter_univ]
    exact hC
  · -- C ∩ Bᶜ = C \ (C ∩ B), a proper difference
    intro B hB
    show C ∩ Bᶜ ∈ L
    have h : C ∩ Bᶜ = C \ (C ∩ B) := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
      tauto
    rw [h]
    exact hL.diff_mem hC hB inter_subset_left
  · -- C ∩ ⋃ fₙ = ⋃ (C ∩ fₙ), still disjoint
    intro f hdisj hf
    show C ∩ ⋃ n, f n ∈ L
    rw [inter_iUnion]
    apply hL.iUnion_mem (fun n => C ∩ f n)
    · intro i j hij
      exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hij)
    · intro n
      exact hf n

--7th Lemma
/-- Minimality: lambdaGen A is inside every λ-system containing A. -/
lemma lambdaGen_subset {A L : Set (Set Ω)} (hL : IsLambdaSys L) (hAL : A ⊆ L) :
    lambdaGen A ⊆ L := by
  intro s hs
  unfold lambdaGen at hs
  exact Set.mem_sInter.mp hs L ⟨hL, hAL⟩

--8th Lemma
--LambdaGen P is closed under interesction
lemma lambdaGen_inter (P : Set (Set Ω)) (hP : IsPiSys P) :
    ∀ A ∈ lambdaGen P, ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P := by
  have hLG := lambdaGen_isLambdaSys P
  -- Step 1: A ∈ P, B ∈ lambdaGen P
  have step1 : ∀ A ∈ P, ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P := by
    intro A hA
    have hsub : lambdaGen P ⊆ {B | A ∩ B ∈ lambdaGen P} := by
      apply lambdaGen_subset (isLambdaSys_inter_slice hLG (subset_lambdaGen P hA))
      -- P ⊆ the slice, because P is a π-system
      intro B hB
      exact subset_lambdaGen P (hP A hA B hB)
    intro B hB
    exact hsub hB
  -- Step 2: A ∈ lambdaGen P, B ∈ lambdaGen P
  intro A hA
  have hsub : lambdaGen P ⊆ {B | A ∩ B ∈ lambdaGen P} := by
    apply lambdaGen_subset (isLambdaSys_inter_slice hLG hA)
    -- P ⊆ the slice, by step 1 with the order of ∩ swapped
    intro B hB
    show A ∩ B ∈ lambdaGen P
    rw [inter_comm]
    exact step1 B hB A hA
  intro B hB
  exact hsub hB

--9th Lemma
lemma isSigmaField_of_lambda_pi (L : Set (Set Ω)) (hL : IsLambdaSys L)
    (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) : IsSigmaField L := by
  refine ⟨?_, ?_, ?_⟩ -- Break the proof into 3 parts
  · exact hL.univ_mem

  · exact hL.compl_mem

  · intro f hf
    -- ⋃ f equals the union of its disjointed version
    rw [← iUnion_disjointed]
    -- λ-systems contain disjoint unions; disjointed f is pairwise disjoint
    apply hL.iUnion_mem (disjointed f) (disjoint_disjointed f)
    -- still to show: each piece disjointed f n is in L
    intro n
    -- disjointed f n is f n with earlier f i's removed one at a time,
    -- so it is enough that L survives "t ↦ t \ f i"
    -- Prove recursivly
    refine disjointedRec (p := (· ∈ L)) ?_ (hf n)
    intro t i ht
    -- t \ f i = t ∩ (f i)ᶜ, which is in L by hπ and compl_mem
    rw [sdiff_eq]
    exact hπ t ht (f i)ᶜ (hL.compl_mem (f i) (hf i))


theorem pi_lambda (P L : Set (Set Ω)) (hP : IsPiSys P) (hL : IsLambdaSys L)
    (hPL : P ⊆ L) : sigmaGen P ⊆ L := by
  -- Step 1: lambdaGen P is a σ-field
  have hσ : IsSigmaField (lambdaGen P) :=
    isSigmaField_of_lambda_pi (lambdaGen P) (lambdaGen_isLambdaSys P) (lambdaGen_inter P hP)
  intro s hs
  -- Step 2: s is in every σ-field containing P, in particular in lambdaGen P
  unfold sigmaGen at hs
  have hsLG : s ∈ lambdaGen P :=
    Set.mem_sInter.mp hs (lambdaGen P) ⟨hσ, subset_lambdaGen P⟩
  -- Step 3: lambdaGen P ⊆ L, since L is a λ-system containing P
  exact lambdaGen_subset hL hPL hsLG

end Math7800.Midterm

#print axioms Math7800.Midterm.lambdaGen_isLambdaSys
#print axioms Math7800.Midterm.subset_lambdaGen
#print axioms Math7800.Midterm.lambdaGen_inter
#print axioms Math7800.Midterm.isSigmaField_of_lambda_pi
#print axioms Math7800.Midterm.pi_lambda
