import StringSearchLean.Table
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option maxHeartbeats 20000000

@[grind]
def decreasing_helper (a b c: Nat): Nat :=
  a * b + c
@[grind]
lemma decreasing_helper_lemma (a1 a2 b1 b2 W: Nat) (h1: b1 < W)  (h2:b2 < W)  : decreasing_helper a1 W b1 < decreasing_helper a2 W b2 ↔ (a1 ≠ a2 -> a1 < a2) ∧ (a1 = a2 -> b1 < b2):=
  by
    constructor
    · intros h'
      simp [decreasing_helper] at h'
      constructor
      · intros neq 
        have neg1: ¬ (a2 * W + b2 < a1 * W + b1 ) := by omega
        by_contra neg2
        have h1' : a2 < a1 := by omega
        have : a2 + 1 ≤ a1 := by omega
        apply neg1
        calc
          a2 * W + b2 < a2 * W + W := by omega
          _           = (a2 + 1) * W := by linarith
          _           ≤ a1 * W := by exact Nat.mul_le_mul_right W h1'
          _ ≤ a1 * W + b1 := by omega
        
      · intros eq
        rw [eq] at h'
        omega
    · simp [decreasing_helper]; intros h1' h2' 
      have : a1 = a2 ∨ ¬ a1 = a2 := by omega
      apply Or.elim this <;> clear this <;> intro eqh
      · specialize h2' eqh
        rw [eqh]
        omega
      · specialize h1' eqh
        have : a1 + 1 ≤ a2 := by omega
        calc
          a1 * W + b1 < a1 * W + W := by omega
          _           = (a1 + 1) * W := by linarith
          _           ≤ a2 * W := by exact Nat.mul_le_mul_right W h1'
          _ ≤ a2 * W + b2 := by omega

method kmp_search (W: Array Nat) (S: Array Nat) return (position: FlaggedNat)
  require (W.size ≥ 1)
  ensures  !position.flag -> ¬∃ val, Matches W 0 S val W.size
  ensures position.flag ->  Matches W 0 S position.val W.size
  do
    let mut j := 0
    let mut k := 0
    let T ← kmp_table W
    let mut result := {flag:= Bool.false, val := 0}
    while j < S.size ∧ k < W.size 
      invariant 0 ≤ j  
      invariant j ≤ S.size
      invariant 0 ≤ k 
      invariant k ≤ W.size
      invariant k ≤ j
      invariant KMPValid_Array W T
      invariant Matches W 0 S (j - k) k
      invariant ∀ offset, offset < j - k → ¬Matches W 0 S offset W.size
      invariant result.flag -> Matches W 0 S result.val W.size
      invariant !result.flag -> k < W.size
      -- done_with ((!result.flag -> j = S.size ∧ k < W.size) ∧ (result.flag -> Matches W 0 S result.val W.size) )
      decreasing decreasing_helper (S.size - j) (W.size + 1) k 
      -- Above line is awkward, ideally I would like to specify
      -- a lexicographic ordering and say, but using the tuple
      -- "decreasing (S.size - j, k)", cause a weird type issue.
      do
      if W[k]! = S[j]! then
        j := j + 1
        k := k + 1
        if k = W.size then 
          result := {flag:= Bool.true, val:= (j - k)}
      else
        if T[k]!.flag then 
          k := T[k]!.val 
        else 
          k:=0
          j := j + 1
    return result


@[loomSpec]
lemma kmp_search_correct (W : Array Nat) (S : Array Nat) :
      triple (with_name_prefix`require(W.size ≥ 1)) (kmp_search W S)
        (fun position =>
          (with_name_prefix`ensures position.flag → Matches W 0 S position.val W.size) ∧
            with_name_prefix`ensures !position.flag → ¬∃ val, Matches W 0 S val W.size) :=
    by
    unfold kmp_search
    (loom_solve)
    all_goals try rw [decreasing_helper_lemma _ _ _ _ _ (by omega) (by omega)]
    all_goals try
    { constructor
      · intro; omega
      · intro _; have : S.size - (j + 1) ≠ S.size - j := by omega
        contradiction }
    all_goals try
    { simp; try rw [<- if_pos_1]
      simp [Matches]
      constructor; omega
      constructor; omega
      intro i iH
      rcases ((by omega): i = k ∨ i < k) with iH | iH
      · rw [iH, if_pos]; congr 1; omega
      · simp [Matches] at invariant_7
        exact invariant_7.2.2 i iH }
    { simp [KMPValid_Array, KMPValid_FlaggedNat] at invariant_6
      rcases invariant_6 with ⟨ bound, invariant_6⟩
      specialize invariant_6 k (by omega)
      simp [if_pos, KMPValid_Nat] at invariant_6
      simp [Matches] at invariant_7
      have invariant_6 := invariant_6.2.1
      simp [Matches] at invariant_6
      simp [Matches]; constructor; omega; constructor; omega
      intros i iH
      have this1 := invariant_6.2.2 i iH
      have this2 := invariant_7.2.2 (k - x[k]!.val + i) (by omega)
      rw [<- this1, this2]
      congr 1; omega }
    { simp [KMPValid_Array, KMPValid_FlaggedNat] at invariant_6
      rcases invariant_6 with ⟨xeq, invariant_6⟩
      specialize invariant_6 k (by omega)
      simp [if_pos, KMPValid_Nat] at invariant_6
      rcases invariant_6 with ⟨xlt, xmatch, xunmatch, greater⟩
      intros offset offsetlt
      rcases ((by omega): offset < j - k ∨  j-k=offset ∨  j-k < offset ) with offsetH | offseteq | offsetgt
      · exact invariant_8 offset offsetH
      · intro offset_match
        simp [Matches, <- offseteq ] at offset_match
        apply if_neg
        rw [offset_match.2 k a_1]
        congr 1; omega
      · intro offset_match
        simp [Matches] at offset_match
        apply if_neg
        have eq1: W[j - offset]! = S[j]! :=
          by
            rw [offset_match.2 (j - offset) (by omega)]
            congr 1; omega
        specialize greater (j - offset) (by omega) (by omega)
        have match_lemma : Matches W (k - (j - offset)) W 0 (j - offset) :=
          by
            simp [Matches]; constructor; omega; constructor; omega
            intros i ijH
            simp [Matches] at invariant_7
            have this1 := invariant_7.2.2 (k - (j - offset) + i) (by omega)
            have this2 := offset_match.2 i (by omega)
            rw [this1, this2]
            congr 1; omega
        specialize greater match_lemma
        have eq2: W[k]! = W[j - offset]! := 
          by
            simp [Matches] at greater
            rw [<- greater.2.2 (j - offset) (by omega)]
            congr 1; omega
        rw [eq2, eq1] }
    { simp [KMPValid_Array, KMPValid_FlaggedNat] at invariant_6
      rcases invariant_6 with ⟨ bound, invariant_6⟩
      specialize invariant_6 k (by omega)
      simp [if_neg_1] at invariant_6
      intros offset offsetlt
      rcases ((by omega): offset < j - k ∨  j-k=offset ∨  j-k < offset ) with offsetH | offseteq | offsetgt
      · exact invariant_8 offset offsetH
      · intro offset_match
        simp [Matches, <- offseteq ] at offset_match
        apply if_neg
        rw [offset_match.2 k a_1]
        congr 1; omega
      · intro offset_match
        simp [Matches] at offset_match
        apply if_neg
        have eq1: W[j - offset]! = S[j]! :=
          by
            rw [offset_match.2 (j - offset) (by omega)]
            congr 1; omega
        have greater := no_match_nonext_of_no_KMPValid
        simp at greater 
        specialize greater W k invariant_6 (j - offset) (by omega)
        have match_lemma : Matches W (k - (j - offset)) W 0 (j - offset) :=
          by
            simp [Matches]; constructor; omega; constructor; omega
            intros i ijH
            simp [Matches] at invariant_7
            have this1 := invariant_7.2.2 (k - (j - offset) + i) (by omega)
            have this2 := offset_match.2 i (by omega)
            rw [this1, this2]
            congr 1; omega
        specialize greater match_lemma
        have eq2: W[k]! = W[j - offset]! := 
          by
            simp [Matches] at greater
            rw [<- greater.2.2 (j - offset) (by omega)]
            congr 1; omega
        rw [eq2, eq1] }
    
    
-- -- /--
-- --   info: DivM.res (some 15)
-- -- -/
-- -- #guard_msgs in
#eval (kmp_search "ABCDABD".toNatArray "ABC ABCDAB ABCDABCDABDE".toNatArray).run




