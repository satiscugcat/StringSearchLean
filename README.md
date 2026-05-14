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

# Velvet Implementation

The corresponding Velvet implementation are as follows:

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
```
