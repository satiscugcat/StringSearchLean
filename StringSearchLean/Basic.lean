import Velvet.Std
import CaseStudies.TestingUtil 

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

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
@[grind]
def Prefix (W: Array Nat) (P: Array Nat) 
  := Matches W 0 P 0 P.size

/--
  For a given index, we say t_i is a KMPValid_Nat if it is the largest number such that
  the suffix of length t_i of the subarray [0..i-1]<both numbers inclusive> is a prefix, 
  and such that improper suffix of length t_i+1 of the subarray [0..i] is not a prefix.
-/
@[grind]
def KMPValid_Nat (W: Array Nat) (i: Nat) (t_i: Nat) : Prop:= 
  Prefix W (W.extract (i - t_i) i) ∧ 
  ¬ Prefix W (W.extract (i - t_i) (i+1))
  ∧ ∀ j > t_i, 
    ¬ (Prefix W (W.extract (i - j) i) ∧ ¬ Prefix W (W.extract (i - j) (i+1)))


@[grind]
def KMPValid_FlaggedNat (W: Array Nat) (i: Nat) (t_i: FlaggedNat) : Prop:= 
  if t_i.flag then KMPValid_Nat W i t_i.val else ¬ ∃ k, KMPValid_Nat W i k

@[grind]
def KMPValid_Array (W: Array Nat) (T: Array FlaggedNat) : Prop :=
  W.size = T.size ∧ 
  ∀ i < T.size, KMPValid_FlaggedNat W i T[i]!

@[grind]
def flagged_to_nat_for_decreasing (o: FlaggedNat) :=
  if o.flag then 0 else o.val + 1

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
      invariant  W[pos]! = W[cnd]! -> KMPValid_FlaggedNat W pos result[cnd]!
      invariant  W[pos]! ≠ W[cnd]! -> KMPValid_Nat W pos cnd
      invariant ∀ i < pos, KMPValid_FlaggedNat W i result[i]!
      invariant KMPValid_Array W (result.extract 0 pos)
      invariant cnd < pos
      
      done_with pos = W.size
      decreasing (W.size - pos)

      do
      let mut cnd' := ({flag:= Bool.true, val := cnd}: FlaggedNat)
      if W[pos]! = W[cnd]! then
        result := result.set! pos (result[cnd]!)
      else
        result := result.set! pos {flag:= Bool.true, val := cnd}
        while cnd'.flag && W[pos]! ≠ W[cnd'.val]! 
        decreasing (flagged_to_nat_for_decreasing cnd')
          do
            cnd' := result[cnd'.val]!
      if !cnd'.flag then cnd := 0 else  cnd := cnd'.val + 1
      pos := pos + 1
    return result


#eval (kmp_table "ABCDABD".toNatArray).run


method kmp_search (W: Array Nat) (S: Array Nat) return (position: Option Nat)
  ensures (match position with | none => ¬∃ val, Matches W 0 S val W.size | some val => Matches W 0 S val W.size)
  do
    let mut j := 0
    let mut k := 0
    let T ← kmp_table W
    let mut result := Option.none
    while j < S.size
      invariant 0 ≤ j ∧ j < T.size
      invariant 0 ≤ k ∧ k < W.size
      decreasing (S.size - j)
      -- Above line is incorrect, ideally I would like to say
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

lemma helper_1 {α: Type} [Inhabited α] {n: Nat} (a: α) (size: n ≥ 1): (Array.replicate n a)[0]! = a :=
  by
    grind


@[loomSpec]
  lemma kmp_table_correct (W : Array Nat) :
      triple (with_name_prefix`require W.size ≥ 1) (kmp_table W)
        (fun T => with_name_prefix`ensures(KMPValid_Array W T)) :=
    by
    unfold kmp_table
    (loom_solve)
    { intros negh
      simp [KMPValid_Nat]
      constructor
      { rw [Array.extract_empty_of_stop_le_start (by grind)]
        simp [Prefix]
        unfold Matches
        
        sorry }
      sorry }
    { sorry }
    { sorry }
    
