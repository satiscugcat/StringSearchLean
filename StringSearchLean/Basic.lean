import Velvet.Std
import CaseStudies.TestingUtil 

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 20000000

def String.toNatArray (s : String) : Array Nat :=
  s.toAsciiByteArray.data.map UInt8.toNat
@[grind]
structure FlaggedNat where
  flag: Bool
  val: Nat
deriving Inhabited, Repr
@[grind]
def Matches (A: Array Nat) (a: Nat) (B: Array Nat) (b: Nat) (n: Nat)
  :=
    n + a ≤ A.size ∧ n + b ≤ B.size ∧ ∀ i < n, A[a + i]! = B[b + i]!



/--
  For a given index, we say t_i is a KMPValid_Nat if it is the largest number such that
  the suffix of length t_i of the subarray [0..i-1]<both numbers inclusive> is a prefix, 
  and such that improper suffix of length t_i+1 of the subarray [0..i] is not a prefix.
-/
@[grind]
def KMPValid_Nat (W: Array Nat) (i: Nat) (t_i: Nat) : Prop:=

  t_i < i ∧ Matches W (i - t_i) W 0 t_i 
  ∧ ¬ Matches W (i - t_i) W 0 (t_i + 1)
  ∧ (∀ j, t_i < j ∧ j < i -> ¬ (Matches W (i - j) W 0 j 
    ∧ ¬ Matches W (i - j) W 0 (j + 1)
    ))


@[grind]
def KMPValid_FlaggedNat (W: Array Nat) (i: Nat) (t_i: FlaggedNat) : Prop:= 
  if t_i.flag then KMPValid_Nat W i t_i.val else ¬ ∃ k, KMPValid_Nat W i k

@[grind]
def KMPValid_Array (W: Array Nat) (T: Array FlaggedNat) : Prop :=
  W.size = T.size ∧ 
  ∀ i < T.size, KMPValid_FlaggedNat W i T[i]!

@[grind]
def flagged_to_nat_for_decreasing (o: FlaggedNat) :=
  if !o.flag then 0 else o.val + 1

-- Definitions
method kmp_table (W: Array Nat) return (T: Array FlaggedNat)
  require W.size ≥ 1
  ensures (KMPValid_Array W T)

  do
    let mut result := Array.replicate W.size {flag := Bool.false, val := 0}
    let mut pos := 1
    let mut cnd := 0
    while pos < W.size 

      invariant 1 ≤ pos ∧ pos ≤ W.size
      invariant W.size = result.size
      invariant ∀ i < pos, KMPValid_FlaggedNat W i result[i]!
      invariant cnd < pos 
      invariant Matches W 0 W (pos - cnd) cnd 
      invariant ∀ j, cnd < j ∧ j < pos → ¬Matches W (pos - j) W 0 j
      done_with pos = W.size
      decreasing (W.size - pos)

      do
      let mut cnd' := ({flag:= Bool.true, val := cnd}: FlaggedNat)
      if W[pos]! = W[cnd]! then
        result := result.set! pos (result[cnd]!)
      else
        result := result.set! pos {flag:= Bool.true, val:= cnd}
        while cnd'.flag && W[pos]! ≠ W[cnd'.val]! 

        invariant cnd'.flag → cnd'.val < pos
        invariant cnd'.flag → Matches W (pos - cnd'.val) W 0 cnd'.val
        invariant ∀ j, (if cnd'.flag then cnd'.val + 1 else 0) < j → j < pos + 1 → ¬Matches W (pos + 1 - j) W 0 j

        decreasing (flagged_to_nat_for_decreasing cnd')
          do
            cnd' := result[cnd'.val]!
      if !cnd'.flag then 
        cnd := 0
        pos := pos + 1
      else  
        cnd := cnd'.val + 1
        pos := pos + 1
    return result


#eval (kmp_table "ABCDABD".toNatArray).run








-- Helper Lemmas

@[grind]
lemma Matches_truncate' (A B : Array Nat) (a b n m : Nat)
    (h : Matches A a B b n) (hm : m ≤ n) :
    Matches A a B b m := by
  unfold Matches at *; exact ⟨by have := h.1; omega, by have := h.2.1; omega, fun i hi => h.2.2 i (by omega)⟩
@[grind]
lemma Matches_not_extend_of_ne (W : Array Nat) (a n : Nat)
    (hne : W[a + n]! ≠ W[n]!) :
    ¬Matches W a W 0 (n + 1) := by
  unfold Matches; push_neg; intro _ _; exact ⟨n, by omega, by simpa⟩
@[grind]
lemma not_Matches_of_not_Matches_shorter {A B : Array Nat} {a b n m : Nat}
    (h : ¬Matches A a B b m) (hm : m ≤ n) :
    ¬Matches A a B b n :=
  fun h' => h (Matches_truncate' _ _ _ _ _ _ h' hm)
@[grind]
lemma Matches_border_trans (W : Array Nat) (p k t : Nat)
    (h1 : Matches W (p - k) W 0 k) (h2 : Matches W (k - t) W 0 t)
    (ht : t ≤ k) (hk : k ≤ p) :
    Matches W (p - t) W 0 t := by
  unfold Matches at *
  refine ⟨by have := h1.1; have := h2.1; omega, by have := h2.2.1; omega, fun i hi => ?_⟩
  have := h1.2.2 (k - t + i) (by omega)
  rw [show p - k + (k - t + i) = p - t + i from by omega, show 0 + (k - t + i) = k - t + i from by omega] at this
  rw [this]; exact h2.2.2 i hi
@[grind]
lemma KMPValid_FlaggedNat_val_lt (W : Array Nat) (i : Nat) (f : FlaggedNat)
    (h : KMPValid_FlaggedNat W i f) (hf : f.flag = true) : f.val < i := by
  unfold KMPValid_FlaggedNat at h; simp [hf] at h; exact h.1
lemma match_bij (W : Array Nat) (pos cnd k : Nat)
    (hm : Matches W (pos - cnd) W 0 (cnd + 1))
    (hk : k < cnd) (hpos : cnd ≤ pos) :
    ∀ i, i < k + 1 → W[(pos - k) + i]! = W[(cnd - k) + i]! := by
  intro i hi
  have h1 := hm.2.2 (cnd - k + i) (by omega); simp at h1
  rw [show pos - k + i = pos - cnd + (cnd - k + i) from by omega]; exact h1
lemma Matches_pos_to_cnd (W : Array Nat) (pos cnd m : Nat)
    (hm : Matches W (pos - cnd) W 0 (cnd + 1))
    (hm_le : m ≤ cnd) (hpos : cnd ≤ pos)
    (h : Matches W (pos - m) W 0 m) :
    Matches W (cnd - m) W 0 m := by
  unfold Matches at *
  refine ⟨by have := hm.1; omega, by have := h.2.1; omega, fun j hj => ?_⟩
  have hbij := hm.2.2 (cnd - m + j) (by omega); simp at hbij
  have hh := h.2.2 j hj
  rw [show pos - m + j = pos - cnd + (cnd - m + j) from by omega] at hh
  rw [← hbij]; exact hh
set_option maxHeartbeats 4000000 in
@[grind]
lemma no_match_nonext_of_no_KMPValid (W : Array Nat) (i : Nat)
    (h : ¬∃ k, KMPValid_Nat W i k) :
    ∀ j, j < i → ¬(Matches W (i - j) W 0 j ∧ ¬Matches W (i - j) W 0 (j + 1)) := by
  by_contra hc; push_neg at hc
  obtain ⟨j, hj_lt, hj_match, hj_not_ext⟩ := hc
  have hfin : Set.Finite {j' | j' < i ∧ Matches W (i - j') W 0 j' ∧ ¬Matches W (i - j') W 0 (j' + 1)} :=
    Set.finite_iff_bddAbove.mpr ⟨i, fun x hx => le_of_lt hx.1⟩
  set S := hfin.toFinset
  have hne : S.Nonempty := ⟨j, hfin.mem_toFinset.mpr ⟨hj_lt, hj_match, hj_not_ext⟩⟩
  set j_max := Finset.max' S hne
  have hmem := hfin.mem_toFinset.mp (Finset.max'_mem S hne)
  apply h
  exact ⟨j_max, hmem.1, hmem.2.1, hmem.2.2, fun j' ⟨hgt, hlt⟩ hconj =>
    Nat.lt_irrefl j' (lt_of_le_of_lt (Finset.le_max' S _ (hfin.mem_toFinset.mpr ⟨hlt, hconj.1, hconj.2⟩)) hgt)⟩
@[grind]
lemma KMPValid_extend (W : Array Nat) (pos cnd t : Nat)
    (hm : Matches W (pos - cnd) W 0 (cnd + 1))
    (hk : KMPValid_Nat W cnd t)
    (hmax : ∀ j, cnd < j → j < pos → ¬Matches W (pos - j) W 0 j)
    (hpos : cnd < pos) :
    KMPValid_Nat W pos t := by
  have ht_lt_cnd := hk.1
  refine ⟨by omega, ?_, ?_, ?_⟩
  · exact Matches_border_trans W pos cnd t (Matches_truncate' _ _ _ _ _ _ hm (by omega)) hk.2.1 (by omega) hpos.le
  · intro habs
    apply hk.2.2.1
    have hbij := match_bij W pos cnd t hm ht_lt_cnd hpos.le
    unfold Matches at habs ⊢
    exact ⟨by have := hm.1; omega, by have := habs.2.1; omega,
      fun i hi => by rw [← hbij i hi]; exact habs.2.2 i hi⟩
  · intro j ⟨hgt, hlt⟩ hconj
    by_cases hjcnd : j > cnd
    · exact hmax j hjcnd hlt hconj.1
    · by_cases hjeq : j = cnd
      · subst hjeq; exact hconj.2 hm
      · have hjlt : j < cnd := by omega
        have hbij := match_bij W pos cnd j hm hjlt hpos.le
        have hm_cnd := Matches_pos_to_cnd W pos cnd j hm hjlt.le hpos.le hconj.1
        have hne_cnd : ¬Matches W (cnd - j) W 0 (j + 1) := by
          intro habs; apply hconj.2
          unfold Matches at habs ⊢
          exact ⟨by have := hm.1; omega, by have := habs.2.1; omega,
            fun i hi => by rw [hbij i hi]; exact habs.2.2 i hi⟩
        exact hk.2.2.2 j ⟨hgt, hjlt⟩ ⟨hm_cnd, hne_cnd⟩
@[grind]
lemma KMPValid_extend_neg (W : Array Nat) (pos cnd : Nat)
    (hm : Matches W (pos - cnd) W 0 (cnd + 1))
    (hneg : ¬∃ k, KMPValid_Nat W cnd k)
    (hmax : ∀ j, cnd < j → j < pos → ¬Matches W (pos - j) W 0 j)
    (hpos : cnd < pos) :
    ¬∃ k, KMPValid_Nat W pos k := by
  have hno := no_match_nonext_of_no_KMPValid W cnd hneg
  intro ⟨k, hk_lt, hk_match, hk_not_ext, hk_max⟩
  by_cases hk_ge : k ≥ cnd
  · rcases Nat.eq_or_lt_of_le hk_ge with rfl | hgt
    · exact hk_not_ext hm
    · exact hmax k hgt hk_lt hk_match
  · push_neg at hk_ge
    have hm_cnd := Matches_pos_to_cnd W pos cnd k hm hk_ge.le hpos.le hk_match
    have hne_cnd : ¬Matches W (cnd - k) W 0 (k + 1) := by
      intro habs; apply hk_not_ext
      have hbij := match_bij W pos cnd k hm hk_ge hpos.le
      unfold Matches at habs ⊢
      exact ⟨by have := hm.1; omega, by have := habs.2.1; omega,
        fun i hi => by rw [hbij i hi]; exact habs.2.2 i hi⟩
    exact hno k hk_ge ⟨hm_cnd, hne_cnd⟩

@[grind]
lemma array_set!_unchanged  (W: Array FlaggedNat) (i pos: ℕ) (val: FlaggedNat) (h1: i < W.size) (h2: pos < W.size) (neq: i ≠ pos) : (W.set! pos val)[i]! = W[i]! :=
 by
   grind
@[grind]
lemma array_set!_changed  (W: Array FlaggedNat) (pos: ℕ) (val: FlaggedNat)  (h2: pos < W.size) : (W.set! pos val)[pos]! = val :=
 by
   grind

lemma Matches_symm (A B: Array Nat) (a b n: Nat) : Matches A a B b n <-> Matches B b A a n
  :=
    by
      constructor <;> simp [Matches] <;> intros h <;> aesop


prove_correct kmp_table by
    loom_solve
    { intros i ih
      have : i = pos ∨ i < pos := by omega
      apply Or.elim this
      · clear this ih; intros ieq
        rw [ieq] at *; clear ieq
        rw [array_set!_changed _ _ _ (by omega)]
        specialize invariant_3 cnd invariant_4
        unfold KMPValid_FlaggedNat at *
        revert invariant_3

        have matches_extra : Matches W (pos - cnd) W 0 (cnd + 1) :=
            by
              simp [Matches]
              constructor; omega
              constructor; omega
              clear i; intros i ih 
              have : i = cnd ∨ i < cnd := by omega
              apply Or.elim this
              · clear this ih;
                intros h; rw[h]; have : pos - cnd + cnd = pos := by omega
                rw [this]; assumption
              · clear this ih
                intros h
                simp [Matches] at invariant_5
                rw [← invariant_5.2.2]
                omega

        rcases result[cnd]!.flag <;> simp <;> intro invariant_3
        · have : _ := KMPValid_extend_neg
          simp at this
          specialize this W pos cnd matches_extra (by assumption) (by assumption) (by assumption)
          exact this 

        · have : _ := KMPValid_extend
          specialize this W pos cnd result[cnd]!.val matches_extra (by assumption) (by assumption) (by assumption)
          exact this
      · clear this ih; intros ilt
        specialize invariant_3 i ilt
        rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
        exact invariant_3 }
    { simp
      have matches_extra : Matches W (pos - cnd) W 0 (cnd + 1) :=
            by
              simp [Matches]
              constructor; omega
              constructor; omega
              intros i ih 
              have : i = cnd ∨ i < cnd := by omega
              apply Or.elim this
              · clear this ih;
                intros h; rw[h]; have : pos - cnd + cnd = pos := by omega
                rw [this]; assumption
              · clear this ih
                intros h
                simp [Matches] at invariant_5
                rw [← invariant_5.2.2]
                omega
      rw [Matches_symm]
      exact matches_extra }
    { intros j jgt jlt match_h
      specialize invariant_6 (j - 1) (by omega) (by omega)
      apply invariant_6; clear invariant_6
      simp [Matches] at *
      constructor; omega
      constructor; omega
      intro i ih
      rw[ ← match_h.2.2 i (by omega)]
      congr 1
      omega }
    { omega }
    { simp at if_pos_1; specialize invariant_7 if_pos_1.1; specialize invariant_8 if_pos_1.1
      rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
      intros h
      specialize invariant_3 cnd'.val invariant_7
      unfold KMPValid_FlaggedNat at invariant_3
      rw [h] at invariant_3
      simp [KMPValid_Nat] at invariant_3
      omega }
    { simp at if_pos_1; specialize invariant_7 if_pos_1.1; specialize invariant_8 if_pos_1.1
      rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
      intros h
      specialize invariant_3 cnd'.val invariant_7
      unfold KMPValid_FlaggedNat at invariant_3
      rw [h] at invariant_3
      simp [KMPValid_Nat] at invariant_3
      constructor; omega
      constructor; omega
      rcases invariant_3 with ⟨val_bound, invariant_3, right ⟩; clear right
      simp [Matches] at invariant_3
      simp [Matches] at invariant_8
      rcases invariant_3 with ⟨ _, _, invariant_3⟩
      rcases invariant_8 with ⟨_, _, invariant_8⟩
      simp; intros i ih
      specialize invariant_3 i (by omega)
      specialize invariant_8 (cnd'.val - result[cnd'.val]!.val + i) (by omega)
      rw [<- invariant_3, <- invariant_8]
      congr 1
      omega }
    { simp at if_pos_1
      specialize invariant_7 if_pos_1.1; specialize invariant_8 if_pos_1.1
      rw [if_pos_1.1] at invariant_9; simp at invariant_9
      rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
      intros j jgt jlt
      have : cnd'.val + 1 < j ∨ j = cnd'.val + 1 ∨ j < cnd'.val + 1 := by omega
      rcases this with jH | jH | jH
      · apply invariant_9 <;> assumption
      · intros jmatch; apply if_pos_1.2
        simp [Matches] at jmatch
        rw [jH] at jmatch
        rw [<- jmatch.2.2 cnd'.val (by omega)]
        congr 1; omega
      · clear jlt; revert jH; intro jlt        
        specialize invariant_3 cnd'.val invariant_7
        simp [KMPValid_FlaggedNat] at invariant_3
        have h_nb : Matches W (cnd'.val - (j - 1)) W 0 (j - 1) ->
              Matches W (cnd'.val - (j - 1)) W 0 j := 
             by
               revert invariant_3 jgt
               rcases result[cnd'.val]!.flag <;> simp <;> intros jgt invariant_3 match_h
               · have := no_match_nonext_of_no_KMPValid W cnd'.val (by simp; exact invariant_3) (j-1) (by omega)
                 simp at this
                 have this2 : j - 1 + 1 = j := by omega
                 rw [this2] at this
                 apply this; assumption
               · simp [KMPValid_Nat] at invariant_3
                 have := invariant_3.2.2.2 (j - 1) (by omega) (by omega) match_h
                 have this2: j - 1 + 1 = j := by omega
                 rw [this2] at this; assumption
        intros hmatch; apply if_pos_1.2
        
        have eq1: W[pos]! = W[j-1]! :=
          by
            simp [Matches] at hmatch
            rw[<- hmatch.2.2 (j - 1) (by omega)]
            congr 1; omega
        have eq2: W[cnd'.val]! = W[j-1]! :=
          by
            have lower_match : Matches W (cnd'.val - (j - 1)) W 0 (j - 1) :=
              by
                simp [Matches]; simp[Matches] at invariant_8; simp[Matches] at hmatch
                constructor; omega
                constructor; omega
                intros i iH
                have this1 := invariant_8.2.2 (cnd'.val - (j - 1) + i) (by omega)
                have this2 := hmatch.2.2 i (by omega)
                rw [<- this2]
                rw [<- this1]
                congr 1; omega
            specialize h_nb lower_match
            simp [Matches] at h_nb
            rw [<- h_nb.2.2 (j-1) (by omega)]
            congr 1; omega
        rw [eq1, eq2]
    }
    { simp at if_pos_1; specialize invariant_7 if_pos_1.1; specialize invariant_8 if_pos_1.1
      rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
      specialize invariant_3 cnd'.val invariant_7
      unfold KMPValid_FlaggedNat at invariant_3
      simp [flagged_to_nat_for_decreasing]
      rw [if_pos_1.1]
      simp
      revert invariant_3
      rcases result[cnd'.val]!.flag 
      · simp
      · simp; intros invariant_3 
        simp [KMPValid_Nat] at invariant_3
        exact invariant_3.1 }
    { simp
      intros j jgt jlt 
      specialize invariant_6 (j - 1) (by omega) (by omega)
      intro negh
      apply invariant_6
      have : pos - (j - 1) = pos + 1 - j := by omega
      rw [this]
      apply Matches_truncate' _ _ _ _ _ _ negh (by omega) }
    { clear invariant_7 invariant_8 invariant_9 done_2 cnd' if_pos_1
      intros i ilt
      have : i = pos ∨ i < pos := by omega
      apply (Or.elim this) <;> clear ilt this <;> intro ih
      · rw [ih]; clear i ih
        rw [array_set!_changed _ _ _ (by omega)]
        simp [KMPValid_FlaggedNat, KMPValid_Nat]
        constructor; assumption
        constructor; rw [Matches_symm]; assumption
        constructor
        · intro h; simp [Matches] at h
          apply if_neg
          have := h.2.2 cnd (by omega)
          rw [← this]; congr 1; omega
        · intros j jgt jlt h
          specialize invariant_6 j jgt jlt; contradiction
      · rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
        apply invariant_3; exact ih }
    { omega }
    { clear invariant_7 invariant_8 invariant_9 done_2 cnd' if_neg_1
      intros i ilt
      have : i = pos ∨ i < pos := by omega
      apply (Or.elim this) <;> clear ilt this <;> intro ih
      · rw [ih]; clear i ih
        rw [array_set!_changed _ _ _ (by omega)]
        simp [KMPValid_FlaggedNat, KMPValid_Nat]
        constructor; assumption
        constructor; rw [Matches_symm]; assumption
        constructor
        · intro h; simp [Matches] at h
          apply if_neg
          have := h.2.2 cnd (by omega)
          rw [← this]; congr 1; omega
        · intros j jgt jlt h
          specialize invariant_6 j jgt jlt; contradiction
      · rw [array_set!_unchanged _ _ _ _ (by omega) (by omega) (by omega)]
        apply invariant_3; exact ih }
    { simp at if_neg_1
      rw [if_neg_1] at done_2
      simp at done_2
      specialize invariant_8 if_neg_1
      specialize invariant_7 if_neg_1
      rw [Matches_symm] at invariant_8
      simp [Matches]
      constructor; omega
      constructor; omega
      
      simp [Matches] at invariant_8
      rcases invariant_8 with ⟨_, _, invariant_8⟩
      
      intros i ih
      have : i = cnd'.val ∨ i < cnd'.val := by omega
      apply Or.elim this <;> clear ih this <;> intro ih
      · rw [ih, <- done_2]
        congr 1; omega
      · revert ih; revert i; exact invariant_8 }
    { omega }

    



    
@[grind]
def decreasing_helper (a b c: Nat): Nat :=
  a * 10^b + c
method kmp_search (W: Array Nat) (S: Array Nat) return (position: Option Nat)
  require (W.size ≥ 1)
  ensures (match position with | none => ¬∃ val, Matches W 0 S val W.size | some val => Matches W 0 S val W.size)
  do
    let mut j := 0
    let mut k := 0
    let T ← kmp_table W
    let mut result := Option.none
    while j < S.size
      invariant 0 ≤ j ∧ j ≤ T.size
      invariant 0 ≤ k ∧ k ≤ W.size
      decreasing decreasing_helper (S.size - j) W.size k 
      -- Above line is awkward, ideally I would like to say
      -- "decreasing (S.size - j, k)", since the natural lean4
      -- ordering is the lexicographic one, but that seems to
      -- cause a weird type issue.
      do
      if W[k]! = S[j]! then
        j := j + 1
        k := k + 1
        if k = W.size then 
          result := Option.some (j - k)
          break
      else
        if T[k]!.flag then 
          k := T[k]!.val 
        else 
          k:=0
          j := j + 1
    return result


-- /--
--   info: DivM.res (some 15)
-- -/
-- #guard_msgs in
#eval (kmp_search "ABCDABD".toNatArray "ABC ABCDAB ABCDABCDABDE".toNatArray).run
