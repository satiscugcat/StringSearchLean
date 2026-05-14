# Background

This repository contains a formalisation of the [Knuth-Morris-Pratt algorithm](https://en.wikipedia.org/wiki/Knuth%E2%80%93Morris%E2%80%93Pratt_algorithm) for searching through a string. Given a text of length `n`, and a search string of length `m`, the KMP algorithm describes a way to find an instance of the search string within the text in `O(m+n)` time and `O(m)` space. Specifically, the chosen implementation returns the starting index of the first occurence of the string, and reports if there are none.

The KMP algorithm consists of two phases. The first phase involves pre-processing of the search string to build a look-up table. The second phase consists of the actual search. Whenever a mis-match occurs during the search, the table is consulted for switching of the text and search string pointers.

Description of the algorithms for the two phases as on Wikipedia:
```
algorithm kmp_table:
    input:
        an array of characters, W (the word to be analyzed)
    output:
        an array of integers, T (the table to be filled)

    define variables:
        an integer, pos ← 1 (the current position we are computing in T)
        an integer, cnd ← 0 (the zero-based index in W of the next character of the current candidate substring)

    let T[0] ← -1

    while pos < length(W) do
        if W[pos] = W[cnd] then
            let T[pos] ← T[cnd]
        else
            let T[pos] ← cnd
            while cnd ≥ 0 and W[pos] ≠ W[cnd] do
                let cnd ← T[cnd]
        let pos ← pos + 1, cnd ← cnd + 1

    let T[pos] ← cnd (only needed when all word occurrences are searched)
```

```
algorithm kmp_search:
    input:
        an array of characters, S (the text to be searched)
        an array of characters, W (the word sought)
    output:
        an array of integers, P (positions in S at which W is found)
        an integer, nP (number of positions)

    define variables:
        an integer, j ← 0 (the position of the current character in S)
        an integer, k ← 0 (the position of the current character in W)
        an array of integers, T (the table, computed elsewhere)

    let nP ← 0

    while j < length(S) do
        if W[k] = S[j] then
            let j ← j + 1
            let k ← k + 1
            if k = length(W) then
                (occurrence found, if only first occurrence is needed, m ← j - k may be returned here)
                let P[nP] ← j - k, nP ← nP + 1
                let k ← T[k] (T[length(W)] can't be -1)
        else
            let k ← T[k]
            if k < 0 then
                let j ← j + 1
                let k ← k + 1
```

# Formalisation within LEAN4 using Velvet

This section describes the details of the Velvet implementation, along with elaboration the properties proven about it.

## Implementation Code

in `StringSearchLean/Table.lean`
```lean 
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
```

in `StringSearchLean/Basic.lean`
```lean
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
      decreasing decreasing_helper (S.size - j) (W.size + 1) k 
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
```

## Pre-requisite Definitions used for Specification

```lean
structure FlaggedNat where
  flag: Bool
  val: Nat
deriving Inhabited, Repr
```
The flag in the FlaggedNat structure is used to signal whether a number is "valid", as opposed to the `-1` that is used in the original description of the algorithm. If the flag is false, the number is invalid. This structure is used in a manner similar to how an `Option Nat` type would be used. (And indeed, `Option Nat` was used for the initial attempt at specification, but was later discarded. More on this at the end of the README.)

```lean 
def Matches (A: Array Nat) (a: Nat) (B: Array Nat) (b: Nat) (n: Nat)
  :=
    n + a ≤ A.size ∧ n + b ≤ B.size ∧ ∀ i < n, A[a + i]! = B[b + i]!
```

Basic definition for specifying that the length `n` string at index `a` of `A` and index `b` of `B` are the same.

```lean
def KMPValid_Nat (W: Array Nat) (i: Nat) (t_i: Nat) : Prop:=

  t_i < i ∧ Matches W (i - t_i) W 0 t_i 
  ∧ ¬ Matches W (i - t_i) W 0 (t_i + 1)
  ∧ (∀ j, t_i < j ∧ j < i -> ¬ (Matches W (i - j) W 0 j 
    ∧ ¬ Matches W (i - j) W 0 (j + 1)
    ))
```

For a given index, we say `t_i` is a `KMPValid_Nat` if it is the _largest_ number such that the suffix of length `t_i` of the subarray `W[0..i-1]`(both indices inclusive) is a prefix, and such that the suffix of length `t_i+1` of the subarray `W[0..i]` is not a prefix.

```lean
def KMPValid_FlaggedNat (W: Array Nat) (i: Nat) (t_i: FlaggedNat) : Prop:= 
  if t_i.flag then KMPValid_Nat W i t_i.val else ¬ ∃ k, KMPValid_Nat W i k
```
If the flag of `t_i: FlaggedNat` is true, then the underlying `t_i.val` must be `KMPValid_Nat` at index `i` w.r.t. `W`. Otherwise, there must exist no natural number for which is `KMPValid_Nat` at index `i` w.r.t. `W`. 

```lean
def KMPValid_Array (W: Array Nat) (T: Array FlaggedNat) : Prop :=
  W.size = T.size ∧ 
  ∀ i < T.size, KMPValid_FlaggedNat W i T[i]!
```
This is the specification of the output of `kmp_table`. Which requires that every corresponding `FlaggedNat` in `T` must be valid as defined above.

```lean
def flagged_to_nat_for_decreasing (o: FlaggedNat) :=
  if !o.flag then 0 else o.val + 1
```
This is a function used for the temrination condition of the inner while loop of `kmp_table`.

```lean
def decreasing_helper (a b c: Nat): Nat :=
  a * b + c
  
lemma decreasing_helper_lemma (a1 a2 b1 b2 W: Nat) (h1: b1 < W)  (h2:b2 < W)  : decreasing_helper a1 W b1 < decreasing_helper a2 W b2 ↔ (a1 ≠ a2 -> a1 < a2) ∧ (a1 = a2 -> b1 < b2):= ...
```
This function is used for the termination condition of the while loop `kmp_search`, it comes with a lemma stating that if the 2nd argument is kept fixed and is always greater than the 3rd argument, then the ordering on the result of the function follows depending on the arguments is equivalent to the lexicographic ordering on the 1st and 3rd arguments. From what I could try, Velvet does not support orderings other than the simple one on natural numbers for describing termination conditions, so this function was used to get around that restriction.


## Properties Proven
Both implementations have the same precondition, in that they require the search string `W` to be non-empty.
- `kmp_table`- It is proven that `KMPValid_Array W T` where `T: Array FlaggedNat` is the resultant table built by the algorithm, where `KMPValid_Array` is described above.
- `kmp_search` - Two postconditions are proven. `!position.flag -> ¬∃ val, Matches W 0 S val W.size` and `position.flag ->  Matches W 0 S position.val W.size`. This means that if the flag in the result is set to true, then the returned index is indeed correct. Otherwise, the search text is not present in the string. Thus the correctness of the search algorithm is proven.


# AI Usage Disclaimer

I used [Aristotle](https://aristotle.harmonic.fun/) quite a bit in the completion of this project. In particular, it wrote many of the lemmas in `StringSearch/Table.lean`. Once the initial bugs were fixed (see below) and the implemenation was done, the development cycle consisted of me working on the project during my waking hours, then sending it off to Aristotle to make further progress while I slept.
- The AI made mistakes in invariant specification.
- Sometimes the AI would add unnecessary lemmas or unnecessary hypotheses in lemmas whose proofs could be simplified.
- Due to the long elaboration time involved in `loom_solve` it would fail at completing proofs by itself as iteration would take too long.
- Overall, progress was still sped up by quite a bit, and the lemmas were critical to the completion of the proof (while also guiding me towards understanding what the final proof would look like).

# Issues encountered and potential improvements to Velvet
Here are some of the issues I faced:
- Errors caused by usage of Option Types: In the first few commits, it can be seen that I used option types to define the algorithm instead of `FlaggedNat`. However, this caused errors when trying to use `loom_solve`, which complained about an error in some unnamed invariant.

```lean
method kmp_table (W: Array Nat) return (T: Array (Option Nat))
  do
    let mut result := Array.replicate W.size Option.none
    let mut pos := 1
    let mut cnd := 0
    while pos < W.size do
      if W[pos]! = W[cnd]! then
        result := result.set! pos (result[cnd]!)
      else
        result := result.set! pos (Option.some cnd)
        let mut cnd' := Option.some cnd
        while cnd' ≠ Option.none && W[pos]! ≠ W[cnd]! do
          match cnd' with
          | none => cnd' := cnd'
          | some val =>
            cnd' := result[val]!
            match cnd' with
            | none => cnd' := cnd'
            | some val' => cnd := val'
        pos := pos + 1
        match cnd' with
        | none => cnd := 0
        | some val => cnd := val + 1
    return result
```
- Weird panic error caused by maxHeartbeats not being set to a high value: Described in this [issue](https://github.com/verse-lab/loom/issues/34) I created. It is not apparent what the cause of the error is, and potentially at the very least a better error message could be used.

- Error in trying to use non-Nat values in `decreasing` clause: Despite LEAN supporting different sorts of termination conditions, Velvet does not seem to do so (from what I could try). Either this could be extended as a feature or the documentation could be updated to reflect it.

- Long elaboration times: This is more of a nitpick but I'm putting this here just to acknowledge that I did find the elaboration times quite large (at times upto 15 minutes on my machine), which caused issues as it discouraged me from rewriting previously defined lemmas or introducing new ones. I imagine this isn't easy to fix at all however, and is probably already a goal the team is pursuing.


